// obligation_key_divergence_pin — the MEASURED obligation-identity divergence
// (cutover item 0.4, docs/plans/2026-07-27-trust-ir-first-cutover.md §3.2.1) and
// the stable key that resolves it (work item T9,
// `trust_types::obligation_identity`).
//
// THE TWO LANES, ONE FIXTURE. `fixtures/obligation-key-divergence/fixture.rs` holds
// three functions: `contract_div_index` (an authored `requires`/`ensures` contract
// PLUS a slice index and a division), `add3` (the plan's nested-`+` collision case),
// and `macro_div` (a macro-expanded division). It was compiled twice at superproject
// commit 49a3545dfcd with the stage2 trustc stamped df16f7c43af
// (aarch64-apple-darwin), and the raw outputs are committed beside it:
//
//   * MIR lane (extraction → vcgen → verifier_api mint):
//       trustc --crate-type=lib --crate-name fixture -Ztrust-verify=on \
//              -Ztrust-policy=advisory -Ztrust-verify-output=json fixture.rs
//     → the three `TRUST_JSON:` `function_result` lines, verbatim, in
//       `mir-lane-rows.jsonl`. Row identity = `obligation_id` minted in
//       `crates/trust-source-contract/src/lib.rs` (`obligation_id`/`contract_id`
//       for the contract bundle; `format!("vc:{}:{}:{}", …, index)` for safety VCs).
//       `crates/trust-mir-extract/src/verifier_api.rs` re-exports it since
//       ca0ddf652c moved the single implementation there.
//   * Direct lane (THIR → trust-ir Module):
//       trustc --crate-type=lib --crate-name fixture -Ztrust-verify=off \
//              -Ztrust-ir-lower -Ztrust-dump=ir:<dir> fixture.rs
//     → `<dir>/fixture.trust-ir.txt`, verbatim, as `direct-lane.trust-ir.txt`.
//       Obligation-shaped rows = `assert … ; #proof: <tag>` instructions.
//
// Both runs were re-run and compared: the direct lane is byte-deterministic, and
// the MIR lane's `function_result` rows are byte-deterministic in every field the
// pins read — `time_ms` is wall-clock and may differ between runs, which is why no
// pin reads it. Do not hand-edit the frozen artifacts; on a mint or span-shaping
// change re-take BOTH with the commands above.
//
// WHAT THE ORDINAL `obligation_id` GOT WRONG (measured on the artifacts):
//   1. One carrier index per function, interleaved across kinds
//      (`bounds_check:0, arithmetic_safety:1, postcondition:2,
//      arithmetic_safety:3`): a removed obligation renumbers every later one.
//   2. Same-span twins are REAL: one source division mints TWO rows of one kind at
//      the IDENTICAL stored span with distinct claim digests.
//   3. Checked-add and macro rows carry DEGENERATE point spans (lo == hi), macro
//      rows at the CALLSITE.
//   4. The LO-edge triple both lanes share is not injective.
//
// So the ordinal stays the private binding/certificate token (docs/TCB.md) and is
// never a comparison key. THE STABLE KEY (`<def_path>#<local id>`,
// `trust_types::obligation_identity`) is derived here from the SAME frozen rows
// and the fixture's source text, through the very functions trustc calls at
// transport emission, and the pins below hold what it must do with them:
//   A. every row of every function gets a distinct key — twins included;
//   B. removing an obligation leaves every other key alone (fixes 1);
//   C. twenty comment lines and an unrelated function inserted above the code,
//      or a line inserted inside a function above an obligation, leave every key
//      alone, and only the edited function's source digest moves;
//   D. a span anchors on the statement around its START, so a point span is
//      anchored (fixes 3), and twins differ only in `nth` (fixes 2);
//   E. a moved or renamed function keeps its local ids (the def path is outside
//      the hash);
//   F. the order the compiler emits rows in decides no key a row's content can
//      decide: reversed emission keeps every distinguishable row's key, and
//      gives each twin group the same keys;
//   G. a reflow (`a + b + c` split over three lines) keeps every key AND the
//      function's source digest — the digest and the anchors read the same
//      tokens, so "unchanged source" never disagrees with "unchanged keys".
//   H. a row's END decides no key: every frozen row re-published as the point at
//      its start (what another compile publishes for the same obligation,
//      measured 2026-10-10 by tests/run-make/trust-obligation-ids) keeps its key.
// Pin 6 (the mint-format census, read live) stays: the ordinal mint is untouched
// and the frozen artifacts are evidence of exactly that mint.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_types::SourceSpan;
use trust_types::obligation_identity::{
    AnchorInput, KeyedRow, LineIndex, anchor, function_source_digest, local_ids, obligation_key,
    row_anchor, row_discriminator, span_position,
};

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is <repo>/crates/trust-types.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").canonicalize().expect("repo root")
}

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("obligation-key-divergence")
}

/// One MIR-lane public result row, projected to its identity components.
#[derive(Debug, Clone, PartialEq, Eq)]
struct MirRow {
    function: String,
    obligation_id: String,
    kind: String,
    description: String,
    claim_digest: String,
    /// (line_start, col_start, line_end, col_end) — trust_types::SourceSpan fields.
    span: (u64, u64, u64, u64),
}

fn mir_rows() -> Vec<MirRow> {
    let raw = std::fs::read_to_string(fixture_dir().join("mir-lane-rows.jsonl"))
        .expect("mir-lane-rows.jsonl present");
    let mut rows = Vec::new();
    for line in raw.lines() {
        // The artifact is the compiler's stderr lines verbatim, prefix included.
        let payload = line.strip_prefix("TRUST_JSON:").expect("verbatim TRUST_JSON line");
        let doc: serde_json::Value = serde_json::from_str(payload).expect("jsonl line parses");
        assert_eq!(doc["type"], "function_result", "artifact holds only function_result docs");
        let function = doc["function"].as_str().expect("function name").to_string();
        for r in doc["results"].as_array().expect("results array") {
            let loc = &r["location"];
            rows.push(MirRow {
                function: function.clone(),
                obligation_id: r["obligation_id"].as_str().expect("obligation_id").to_string(),
                kind: r["kind"].as_str().expect("kind").to_string(),
                description: r["description"].as_str().expect("description").to_string(),
                claim_digest: r["claim_digest_sha256"].as_str().expect("digest").to_string(),
                span: (
                    loc["line_start"].as_u64().expect("line_start"),
                    loc["col_start"].as_u64().expect("col_start"),
                    loc["line_end"].as_u64().expect("line_end"),
                    loc["col_end"].as_u64().expect("col_end"),
                ),
            });
        }
    }
    rows
}

/// One direct-lane obligation-shaped instruction: `assert … ; #proof: <tag> ; #loc: f l c`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DirectAssert {
    function: String,
    proof_tag: String,
    /// (file index, line, col) — the `; #loc:` LO-only triple the artifact stores.
    loc: (u64, u64, u64),
}

fn direct_asserts() -> Vec<DirectAssert> {
    let raw = std::fs::read_to_string(fixture_dir().join("direct-lane.trust-ir.txt"))
        .expect("direct-lane.trust-ir.txt present");
    let mut function = String::new();
    let mut out = Vec::new();
    for line in raw.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("fn @") {
            function = rest.split('(').next().expect("fn name").to_string();
        }
        if !t.starts_with("assert ") {
            continue;
        }
        let proof_tag = t
            .split("; #proof: ")
            .nth(1)
            .expect("assert carries a #proof tag")
            .split_whitespace()
            .next()
            .expect("tag token")
            .to_string();
        let loc_part = t.split("; #loc: ").nth(1).expect("assert carries a #loc");
        let nums: Vec<u64> =
            loc_part.split_whitespace().take(3).map(|n| n.parse().expect("loc number")).collect();
        out.push(DirectAssert {
            function: function.clone(),
            proof_tag,
            loc: (nums[0], nums[1], nums[2]),
        });
    }
    out
}

/// The frozen MIR-lane identity table, in carrier order. If the mint changes shape,
/// this is the table to re-derive — from a fresh run, never by hand.
#[test]
fn mir_lane_rows_are_exactly_the_frozen_table() {
    let expect: Vec<(&str, &str, &str, (u64, u64, u64, u64))> = vec![
        // function, obligation_id, kind, span
        (
            "fixture::contract_div_index",
            "obligation:fixture__contract_div_index:precondition:0",
            "assumption:requires",
            (4, 13, 4, 18),
        ),
        (
            "fixture::contract_div_index",
            "obligation:fixture__contract_div_index:postcondition:1",
            "postcond",
            (5, 12, 5, 23),
        ),
        (
            "fixture::contract_div_index",
            "vc:fixture__contract_div_index:bounds_check:0",
            "slice",
            (7, 4, 7, 9),
        ),
        (
            "fixture::contract_div_index",
            "vc:fixture__contract_div_index:arithmetic_safety:1",
            "divzero",
            (7, 4, 7, 13),
        ),
        (
            "fixture::contract_div_index",
            "vc:fixture__contract_div_index:postcondition:2",
            "postcond",
            (7, 4, 7, 9),
        ),
        (
            "fixture::contract_div_index",
            "vc:fixture__contract_div_index:arithmetic_safety:3",
            "divzero",
            (7, 4, 7, 13),
        ),
        ("fixture::add3", "vc:fixture__add3:arithmetic_safety:0", "overflow:add", (15, 4, 15, 4)),
        ("fixture::add3", "vc:fixture__add3:arithmetic_safety:1", "overflow:add", (15, 4, 15, 4)),
        (
            "fixture::macro_div",
            "vc:fixture__macro_div:arithmetic_safety:0",
            "divzero",
            (26, 4, 26, 4),
        ),
        (
            "fixture::macro_div",
            "vc:fixture__macro_div:arithmetic_safety:1",
            "divzero",
            (26, 4, 26, 4),
        ),
    ];
    let rows = mir_rows();
    let got: Vec<(&str, &str, &str, (u64, u64, u64, u64))> = rows
        .iter()
        .map(|r| (r.function.as_str(), r.obligation_id.as_str(), r.kind.as_str(), r.span))
        .collect();
    assert_eq!(got, expect, "the MIR-lane identity table moved: re-take BOTH lane artifacts");
    // Every claim digest is distinct — the same-span duplicate pairs below are
    // genuinely different propositions, not double-published rows.
    let mut digests: Vec<&str> = rows.iter().map(|r| r.claim_digest.as_str()).collect();
    digests.sort_unstable();
    digests.dedup();
    assert_eq!(digests.len(), rows.len(), "claim digests must be pairwise distinct");
}

/// Pin 4 — the direct lane's obligation surface today: exactly four
/// obligation-shaped asserts (`div_nonzero` ×2, `no_overflow` ×2). No slice
/// bounds obligation is born, and no contract clause reaches the module text —
/// the lane itself declares `structural-parity-only-v1` (checked at the source
/// below, so a capability upgrade fails this pin and forces a re-measure).
#[test]
fn direct_lane_births_exactly_the_four_known_asserts_and_no_contracts() {
    let asserts = direct_asserts();
    let expect = vec![
        DirectAssert {
            function: "contract_div_index".into(),
            proof_tag: "div_nonzero".into(),
            loc: (0, 7, 4),
        },
        DirectAssert { function: "add3".into(), proof_tag: "no_overflow".into(), loc: (0, 15, 4) },
        DirectAssert { function: "add3".into(), proof_tag: "no_overflow".into(), loc: (0, 15, 4) },
        DirectAssert {
            function: "macro_div".into(),
            proof_tag: "div_nonzero".into(),
            loc: (0, 26, 4),
        },
    ];
    assert_eq!(
        asserts, expect,
        "the direct lane's obligation surface moved: re-take BOTH lane artifacts"
    );

    let text = std::fs::read_to_string(fixture_dir().join("direct-lane.trust-ir.txt")).unwrap();
    assert!(!text.contains("requires"), "no contract obligation is born in the direct lane today");
    assert!(!text.contains("ensures"), "no contract obligation is born in the direct lane today");
    assert!(
        !text.contains("bounds"),
        "no slice bounds obligation is born in the direct lane today"
    );

    // The lane's own self-declaration, read live from the producer source —
    // and read as the const's ASSIGNED variant, not as a substring. The old
    // substring probe (`contains("structural-parity-only-v1")`) stayed
    // textually green across the Step 2/3 capability flip because the variant
    // string survives in source; what this pin needs is the RECORDED tier.
    let crate_module =
        std::fs::read_to_string(repo_root().join("crates/trust-thir-lower/src/crate_module.rs"))
            .expect("crate_module.rs readable");
    let assignment = crate_module
        .split("pub const DIRECT_OBLIGATION_CAPABILITY: DirectObligationCapability =")
        .nth(1)
        .expect("the capability const is declared")
        .split(';')
        .next()
        .expect("the capability const assignment terminates");
    assert!(
        assignment.contains("ObligationBearingPending"),
        "the direct lane's recorded obligation capability changed from \
         obligation-bearing-pending-v2: re-take both lane fixture artifacts and \
         re-derive this pin (assigned variant read live: {assignment:?})"
    );
}

/// Pin 6 — the mint sites themselves, read live (span_normalization_parity
/// style): the safety mint is the carrier-index `format!("vc:{}:{}:{}", …)`
/// (three copies) and the contract mint indexes by CONTRACT position. If either
/// changes, the frozen artifacts above are stale evidence — re-take them.
#[test]
fn mint_sites_still_have_the_pinned_shape() {
    // ca0ddf652c moved the mint into `trust-source-contract`;
    // `trust-mir-extract`'s `verifier_api.rs` is now a re-export of it.
    let api = std::fs::read_to_string(repo_root().join("crates/trust-source-contract/src/lib.rs"))
        .expect("trust-source-contract's lib.rs readable");
    let vc_mints = api.matches(r#""vc:{}:{}:{}""#).count();
    assert_eq!(
        vc_mints, 3,
        "expected exactly the three carrier-index safety mint sites in trust-source-contract \
         (verifier_vc_content_identity_with_source_digest_and_crate_name, \
         function_to_verifier_api_bundle_for_target, \
         trust_vc_mir_memory_metadata); found {vc_mints} — \
         the mint changed, re-take the frozen artifacts"
    );
    assert!(
        api.contains("contract.stable_source_id(&function.def_path, index)"),
        "the contract mint no longer indexes by contract position — re-take the artifacts"
    );
    assert!(
        api.contains(r#""obligation:{}:{}:{}""#),
        "the contract-lane obligation id format moved — re-take the artifacts"
    );
}

// ---------------------------------------------------------------------------
// The stable key (T9) over the same frozen rows.
// ---------------------------------------------------------------------------

fn fixture_source() -> String {
    std::fs::read_to_string(fixture_dir().join("fixture.rs")).expect("fixture.rs present")
}

fn source_span(row: &MirRow, line_shift: u32) -> SourceSpan {
    let shift = |line: u64| u32::try_from(line).expect("line fits") + line_shift;
    SourceSpan {
        file: "fixture.rs".to_string(),
        line_start: shift(row.span.0),
        col_start: u32::try_from(row.span.1).expect("col fits"),
        line_end: shift(row.span.2),
        col_end: u32::try_from(row.span.3).expect("col fits"),
    }
}

/// Every row's `<def_path>#<local id>`, in artifact order, computed the way
/// trustc computes it at emission: one anchor per row against the file's text,
/// then one `local_ids` call per function. `shift(row)` is how many lines an
/// edit moved that row down.
fn stable_keys_with(rows: &[MirRow], source: &str, shift: impl Fn(&MirRow) -> u32) -> Vec<String> {
    let lines = LineIndex::new(source);
    let spans: Vec<SourceSpan> = rows.iter().map(|row| source_span(row, shift(row))).collect();
    let anchors: Vec<String> = rows
        .iter()
        .zip(&spans)
        .map(|(row, span)| {
            let input = AnchorInput::of(Some(span), &row.description, Some((source, &lines)));
            // The strict anchor accepts every frozen span, so the compiler's
            // anchor (which degrades instead of refusing) is the strict one.
            let strict = anchor(input).expect("every frozen span lies inside fixture.rs");
            let compiled = row_anchor(input);
            assert!(!compiled.degraded);
            assert_eq!(compiled.anchor, strict);
            strict
        })
        .collect();
    let discriminators: Vec<String> =
        rows.iter().map(|row| row_discriminator(&row.description)).collect();
    let mut by_function: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    for (index, row) in rows.iter().enumerate() {
        by_function.entry(row.function.as_str()).or_default().push(index);
    }
    let mut keys = vec![String::new(); rows.len()];
    for (function, indices) in by_function {
        let keyed: Vec<KeyedRow<'_>> = indices
            .iter()
            .map(|&i| KeyedRow {
                kind: &rows[i].kind,
                anchor: &anchors[i],
                position: span_position(Some(&spans[i])),
                discriminator: &discriminators[i],
            })
            .collect();
        let ids = local_ids(&keyed).expect("no collision on the fixture");
        for (&i, id) in indices.iter().zip(ids) {
            keys[i] = obligation_key(function, &id);
        }
    }
    keys
}

fn stable_keys(rows: &[MirRow]) -> Vec<String> {
    stable_keys_with(rows, &fixture_source(), |_| 0)
}

/// Pin A — every row of every function gets a distinct key, the twins
/// included: contract_div_index's two divisions at one stored span, add3's two
/// point-span additions, macro_div's two point-span divisions.
#[test]
fn every_row_has_a_distinct_stable_key_twins_included() {
    let rows = mir_rows();
    let keys = stable_keys(&rows);
    let mut distinct = keys.clone();
    distinct.sort_unstable();
    distinct.dedup();
    assert_eq!(distinct.len(), rows.len(), "keys must be pairwise distinct: {keys:#?}");
    for (row, key) in rows.iter().zip(&keys) {
        assert!(key.starts_with(&format!("{}#", row.function)), "{key} names its function");
    }
}

/// Pin B — removing an obligation leaves every other key alone. The ordinal
/// mint numbered the bounds row 0 in ONE interleaved space, so dropping it
/// renumbered every later safety row; the stable key has no such space.
#[test]
fn removing_an_obligation_leaves_every_other_key_alone() {
    let rows = mir_rows();
    let keys = stable_keys(&rows);
    let bounds = rows
        .iter()
        .position(|row| row.obligation_id == "vc:fixture__contract_div_index:bounds_check:0")
        .expect("the bounds row is in the artifact");
    let mut without = rows.clone();
    without.remove(bounds);
    let mut expected = keys.clone();
    expected.remove(bounds);
    assert_eq!(stable_keys(&without), expected);

    // Dropping ONE twin renumbers only that twin cell: the survivor takes nth 0.
    let twin = rows.iter().rposition(|row| row.function == "fixture::add3").expect("add3 rows");
    let mut one_twin = rows.clone();
    one_twin.remove(twin);
    let after = stable_keys(&one_twin);
    for (index, key) in after.iter().enumerate() {
        let original = if index < twin { index } else { index + 1 };
        assert_eq!(key, &keys[original], "only the dropped twin's cell moves");
    }
}

/// Pin C — edits that do not touch an obligation's text do not move its key:
/// twenty comment lines and an unrelated function above everything, and one
/// line inserted inside `contract_div_index` above `xs[i] / d`. Only the edited
/// function's source digest moves.
#[test]
fn unrelated_edits_and_edits_above_an_obligation_keep_every_key() {
    let rows = mir_rows();
    let base = fixture_source();
    let keys = stable_keys(&rows);

    let mut prefix = String::new();
    for n in 0..20 {
        prefix.push_str(&format!("// unrelated comment {n}\n"));
    }
    prefix.push_str("pub fn unrelated(x: u32) -> u32 {\n    x / 3\n}\n");
    let prefix_lines = u32::try_from(prefix.lines().count()).expect("fits");
    let shifted = format!("{prefix}{base}");
    assert_eq!(stable_keys_with(&rows, &shifted, |_| prefix_lines), keys);

    // One line inside contract_div_index, after the body's `{` (line 6): the
    // rows on line 7 move to line 8, the contract rows on lines 4-5 stay.
    let mut lines: Vec<&str> = base.lines().collect();
    lines.insert(6, "    let _unrelated = 1u64;");
    let inside = format!("{}\n", lines.join("\n"));
    let moved = stable_keys_with(&rows, &inside, |row| u32::from(row.span.0 >= 7));
    assert_eq!(moved, keys);

    // The edited function's source digest moves; the untouched ones do not.
    let item = |text: &str, from: usize, to: usize| -> String {
        text.lines().skip(from - 1).take(to - from + 1).collect::<Vec<_>>().join("\n")
    };
    assert_ne!(
        function_source_digest(&item(&base, 3, 8)),
        function_source_digest(&item(&inside, 3, 9))
    );
    assert_eq!(
        function_source_digest(&item(&base, 14, 16)),
        function_source_digest(&item(&inside, 15, 17)),
        "add3 is untouched"
    );
}

/// Pin D — a degenerate point span anchors on its enclosing statement, so the
/// checked-add pair anchors on `a + b + c` and the macro pair on the callsite
/// statement `halve!(a, d)`, and each pair differs only in `nth`.
#[test]
fn point_spans_anchor_on_their_statement_and_twins_differ_only_in_nth() {
    let rows = mir_rows();
    let source = fixture_source();
    let lines = LineIndex::new(&source);
    for function in ["fixture::add3", "fixture::macro_div"] {
        let pair: Vec<&MirRow> = rows.iter().filter(|row| row.function == function).collect();
        assert_eq!(pair.len(), 2);
        let anchors: Vec<String> = pair
            .iter()
            .map(|row| {
                let span = source_span(row, 0);
                anchor(AnchorInput::of(Some(&span), &row.description, Some((&source, &lines))))
                    .expect("anchor")
            })
            .collect();
        assert!(
            anchors[0].starts_with("stmt:"),
            "{function}: a point span anchors on its statement"
        );
        assert_eq!(anchors[0], anchors[1], "{function}: the twins share one anchor");
        let keyed = |row: &MirRow, anchor: &'_ str| -> (String, String, String) {
            (row.kind.clone(), anchor.to_string(), row_discriminator(&row.description))
        };
        let (k0, k1) = (keyed(pair[0], &anchors[0]), keyed(pair[1], &anchors[1]));
        let ids = local_ids(&[
            KeyedRow { kind: &k0.0, anchor: &k0.1, position: (1, 0), discriminator: &k0.2 },
            KeyedRow { kind: &k1.0, anchor: &k1.1, position: (1, 0), discriminator: &k1.2 },
        ])
        .expect("ids");
        assert_ne!(ids[0], ids[1], "{function}: nth separates the twins");
    }
}

/// Pin E — the def path is outside the hash: the same rows under another def
/// path (a moved or renamed function) keep their local ids.
#[test]
fn a_moved_function_keeps_its_local_ids() {
    let rows = mir_rows();
    let keys = stable_keys(&rows);
    let renamed: Vec<MirRow> = rows
        .iter()
        .cloned()
        .map(|mut row| {
            row.function = row.function.replace("fixture::", "fixture::moved::");
            row
        })
        .collect();
    let moved = stable_keys(&renamed);
    for (before, after) in keys.iter().zip(&moved) {
        let id = |key: &str| key.rsplit_once('#').expect("key").1.to_string();
        assert_eq!(id(before), id(after));
        assert_ne!(before, after, "the def path half follows the move");
    }
}

/// Pin F — emission order decides no key that a row's content can decide. With
/// the rows emitted in reverse, every row that differs from its group-mates in
/// position (its span's START: the end is not the obligation's) or description
/// keeps its key, and each group of true twins (same kind, anchor, start and
/// description) is given the same set of keys.
#[test]
fn reversed_emission_moves_no_key_a_rows_content_decides() {
    let rows = mir_rows();
    let keys = stable_keys(&rows);
    let mut reversed_rows = rows.clone();
    reversed_rows.reverse();
    let mut reversed = stable_keys(&reversed_rows);
    reversed.reverse();
    let content = |row: &MirRow| {
        (row.function.clone(), row.kind.clone(), (row.span.0, row.span.1), row.description.clone())
    };
    for (index, row) in rows.iter().enumerate() {
        let twins: Vec<usize> =
            (0..rows.len()).filter(|&other| content(&rows[other]) == content(row)).collect();
        if twins.len() == 1 {
            assert_eq!(reversed[index], keys[index], "{} keeps its key", row.obligation_id);
        } else {
            let mut before: Vec<&String> = twins.iter().map(|&i| &keys[i]).collect();
            let mut after: Vec<&String> = twins.iter().map(|&i| &reversed[i]).collect();
            before.sort();
            after.sort();
            assert_eq!(before, after, "a twin group keeps its keys");
        }
    }
}

/// Pin G — a reflow is not an edit. `add3`'s `a + b + c` split over three
/// lines keeps every key (its point spans still start at `a`; the macro rows
/// below move down two lines) and `add3`'s source digest.
#[test]
fn a_reflow_keeps_every_key_and_the_source_digest() {
    let rows = mir_rows();
    let base = fixture_source();
    let keys = stable_keys(&rows);
    let reflowed = base.replace("    a + b + c\n", "    a\n        + b\n        + c\n");
    assert_ne!(reflowed, base, "the fixture still holds `a + b + c` on one line");
    let moved = stable_keys_with(&rows, &reflowed, |row| if row.span.0 > 15 { 2 } else { 0 });
    assert_eq!(moved, keys);
    let item = |text: &str, from: usize, to: usize| -> String {
        text.lines().skip(from - 1).take(to - from + 1).collect::<Vec<_>>().join("\n")
    };
    assert_eq!(
        function_source_digest(&item(&base, 14, 16)),
        function_source_digest(&item(&reflowed, 14, 18)),
        "a reflow of add3 is not an edit of add3"
    );
}

/// Pin H — a row's END is not the obligation's: the same division is published
/// as a point at its start by one compile and as a range by another, and an
/// unrelated edit can move a function from one to the other (measured
/// 2026-10-10, `tests/run-make/trust-obligation-ids`). Every frozen row
/// re-published as the point at its start keeps its key.
#[test]
fn a_row_republished_as_the_point_at_its_start_keeps_its_key() {
    let rows = mir_rows();
    let keys = stable_keys(&rows);
    assert!(
        rows.iter().any(|row| (row.span.0, row.span.1) != (row.span.2, row.span.3)),
        "the frozen rows include ranges, so this pin compares two span shapes"
    );
    let points: Vec<MirRow> = rows
        .iter()
        .cloned()
        .map(|mut row| {
            row.span = (row.span.0, row.span.1, row.span.0, row.span.1);
            row
        })
        .collect();
    assert_eq!(stable_keys(&points), keys);
}
