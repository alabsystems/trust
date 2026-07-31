// obligation_key_divergence_pin — pins the MEASURED cross-lane obligation-identity
// divergence that cutover item 0.4 (docs/plans/2026-07-27-trust-ir-first-cutover.md,
// §3.2.1) must resolve, so it cannot drift silently while the producer-independent
// gate key is being designed.
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
//       `crates/trust-mir-extract/src/verifier_api.rs` (`obligation_id`/`contract_id`
//       for the contract bundle; `format!("vc:{}:{}:{}", …, index)` for safety VCs).
//   * Direct lane (THIR → trust-ir Module):
//       trustc --crate-type=lib --crate-name fixture -Ztrust-verify=off \
//              -Ztrust-ir-lower -Ztrust-dump=ir:<dir> fixture.rs
//     → `<dir>/fixture.trust-ir.txt`, verbatim, as `direct-lane.trust-ir.txt`.
//       Obligation-shaped rows = `assert … ; #proof: <tag>` instructions.
//
// Both runs were re-run and compared: the direct lane is byte-deterministic, and
// the MIR lane's `function_result` rows are byte-deterministic in every field the
// pins read — `time_ms` is wall-clock and may differ between runs (measured: one
// row flipped 1↔0 ms), which is why no pin reads it. Every assertion below states what IS; none asserts the key item 0.4
// wants to exist.
//
// WHAT THIS BATTERY DETECTS, stated precisely rather than optimistically: pins
// 1, 2, 3 and 5 assert over the FROZEN artifact files, so they detect artifact
// tampering and keep the measured divergence readable — they do NOT detect a
// live producer change (a fix to the trust-mode MIR span collapse, or an
// ordinal-scheme change that keeps the `vc:{}:{}:{}` format string, leaves them
// green on stale artifacts). Only pin 6 (the mint format-string census) and
// pin 4's `structural-parity-only-v1` probe read the live tree. On any mint or
// span-shaping change: re-take BOTH artifacts with the commands above (one
// commit, one trustc stamp for both) and re-derive the expectations; do not
// hand-edit the frozen artifacts.
//
// WHAT THE PIN HOLDS (each has a dedicated test):
//   1. The safety-VC mint is carrier-relative: one index space per function,
//      interleaved across kinds (`bounds_check:0, arithmetic_safety:1,
//      postcondition:2, arithmetic_safety:3`) — a removed VC renumbers survivors.
//   2. Same-anchor duplicates are REAL: one source division mints TWO rows of the
//      same kind at the IDENTICAL stored span with distinct claim digests. Under
//      §3.2.1's fail-closed rule (equal anchor → `ordinal-collision`, run has no
//      rows) today's carrier zeroes any run containing a division.
//   3. The MIR lane's anchor input is destroyed before the mint for two classes:
//      checked-add rows and macro-expanded rows carry DEGENERATE point spans
//      (lo == hi), macro rows at the CALLSITE — although `convert_span` is pinned
//      raw LO+HI (span_normalization_parity.rs) and `--emit=mir` under
//      -Ztrust-verify=off shows real ranges (add3 15:5:15:10 / 15:5:15:14, macro
//      div 19:9:19:16). The damage is trust-mode MIR shaping upstream of the
//      converter: -Ztrust-verify=on MIR already reads 15:5:15:5 / 26:5:26:5.
//   4. The direct lane births only a SUBSET of obligations (its coverage artifact
//      says so: `direct_obligation_capability = "structural-parity-only-v1"`):
//      div_nonzero and no_overflow asserts exist; the slice bounds obligation and
//      both contract obligations are NOT born there today.
//   5. The LO-edge triple both lanes share is NOT an injective anchor: add3's two
//      no_overflow obligations agree on (file, line, col) in BOTH lanes, and
//      contract_div_index's bounds row shares its LO with its div row.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is <repo>/crates/trust-types.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").canonicalize().expect("repo root")
}

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("fixtures").join("obligation-key-divergence")
}

/// One MIR-lane public result row, projected to its identity components.
#[derive(Debug, Clone, PartialEq, Eq)]
struct MirRow {
    function: String,
    obligation_id: String,
    kind: String,
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
        out.push(DirectAssert { function: function.clone(), proof_tag, loc: (nums[0], nums[1], nums[2]) });
    }
    out
}

/// The frozen MIR-lane identity table, in carrier order. If the mint changes shape,
/// this is the table to re-derive — from a fresh run, never by hand.
#[test]
fn mir_lane_rows_are_exactly_the_frozen_table() {
    let expect: Vec<(&str, &str, &str, (u64, u64, u64, u64))> = vec![
        // function, obligation_id, kind, span
        ("fixture::contract_div_index", "obligation:fixture__contract_div_index:precondition:0", "assumption:requires", (4, 13, 4, 18)),
        ("fixture::contract_div_index", "obligation:fixture__contract_div_index:postcondition:1", "postcond", (5, 12, 5, 23)),
        ("fixture::contract_div_index", "vc:fixture__contract_div_index:bounds_check:0", "slice", (7, 4, 7, 9)),
        ("fixture::contract_div_index", "vc:fixture__contract_div_index:arithmetic_safety:1", "divzero", (7, 4, 7, 13)),
        ("fixture::contract_div_index", "vc:fixture__contract_div_index:postcondition:2", "postcond", (7, 4, 7, 9)),
        ("fixture::contract_div_index", "vc:fixture__contract_div_index:arithmetic_safety:3", "divzero", (7, 4, 7, 13)),
        ("fixture::add3", "vc:fixture__add3:arithmetic_safety:0", "overflow:add", (15, 4, 15, 4)),
        ("fixture::add3", "vc:fixture__add3:arithmetic_safety:1", "overflow:add", (15, 4, 15, 4)),
        ("fixture::macro_div", "vc:fixture__macro_div:arithmetic_safety:0", "divzero", (26, 4, 26, 4)),
        ("fixture::macro_div", "vc:fixture__macro_div:arithmetic_safety:1", "divzero", (26, 4, 26, 4)),
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

/// Pin 1 — the safety mint's trailing ordinal is a position in ONE per-function
/// carrier, interleaved across kinds. Per-kind ordinals would read
/// `arithmetic_safety:{0,1}`; the measured carrier reads `{1,3}` because
/// `bounds_check` and the body-aware `postcondition` VC occupy 0 and 2.
#[test]
fn safety_ordinals_are_carrier_relative_not_per_kind() {
    let rows = mir_rows();
    let f1_safety: Vec<&str> = rows
        .iter()
        .filter(|r| r.function == "fixture::contract_div_index")
        .filter(|r| r.obligation_id.starts_with("vc:"))
        .map(|r| r.obligation_id.rsplit(':').next().expect("trailing ordinal"))
        .collect();
    assert_eq!(f1_safety, ["0", "1", "2", "3"], "one interleaved index space per function");
    let f1_kinds: Vec<&str> = rows
        .iter()
        .filter(|r| r.function == "fixture::contract_div_index")
        .filter(|r| r.obligation_id.starts_with("vc:"))
        .map(|r| r.kind.as_str())
        .collect();
    assert_eq!(f1_kinds, ["slice", "divzero", "postcond", "divzero"], "kinds interleave in the same space");
}

/// Pin 2 — the §3.2.1 ordinal-collision class is ALREADY POPULATED: in every
/// function of this fixture, one source construct mints two rows of the same kind
/// at the identical stored span, distinguished only by carrier index (and by
/// claim digest, which the locator does not include).
#[test]
fn same_kind_same_span_duplicates_exist_in_every_function() {
    let rows = mir_rows();
    for (function, kind) in [
        ("fixture::contract_div_index", "divzero"),
        ("fixture::add3", "overflow:add"),
        ("fixture::macro_div", "divzero"),
    ] {
        let pair: Vec<&MirRow> =
            rows.iter().filter(|r| r.function == function && r.kind == kind).collect();
        assert_eq!(pair.len(), 2, "{function}: exactly two {kind} rows");
        assert_eq!(pair[0].span, pair[1].span, "{function}: the two {kind} rows share one stored span");
        assert_ne!(pair[0].claim_digest, pair[1].claim_digest, "{function}: but they are distinct propositions");
        assert_ne!(pair[0].obligation_id, pair[1].obligation_id, "{function}: only the carrier index separates them");
    }
}

/// Pin 3 — anchor-input destruction: checked-add and macro-expanded rows carry
/// DEGENERATE point spans (lo == hi), and the macro rows sit at the CALLSITE
/// (fixture.rs line 26, `halve!(a, d)`) — not at the macro-definition division
/// (line 22, `$x / $d`). `convert_span` itself is pinned raw LO+HI by
/// span_normalization_parity.rs, so this loss happens UPSTREAM, in trust-mode MIR
/// shaping (MEASURED: `--emit=mir -Zmir-include-spans=yes` shows ranges under
/// -Ztrust-verify=off and points under -Ztrust-verify=on). The plain division and
/// the contract clauses keep real ranges — the damage is class-specific.
#[test]
fn checked_add_and_macro_rows_have_collapsed_spans_macro_at_callsite() {
    let rows = mir_rows();
    for r in &rows {
        let degenerate = r.span.0 == r.span.2 && r.span.1 == r.span.3;
        let expect_degenerate =
            r.function == "fixture::add3" || r.function == "fixture::macro_div";
        assert_eq!(
            degenerate, expect_degenerate,
            "span degeneracy is exactly the checked-add + macro classes; row {}",
            r.obligation_id
        );
    }
    // The macro rows' stored line is the invocation (26), not the macro body (22).
    for r in rows.iter().filter(|r| r.function == "fixture::macro_div") {
        assert_eq!(r.span.0, 26, "macro-expanded VC stored at the callsite line");
    }
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
        DirectAssert { function: "contract_div_index".into(), proof_tag: "div_nonzero".into(), loc: (0, 7, 4) },
        DirectAssert { function: "add3".into(), proof_tag: "no_overflow".into(), loc: (0, 15, 4) },
        DirectAssert { function: "add3".into(), proof_tag: "no_overflow".into(), loc: (0, 15, 4) },
        DirectAssert { function: "macro_div".into(), proof_tag: "div_nonzero".into(), loc: (0, 26, 4) },
    ];
    assert_eq!(asserts, expect, "the direct lane's obligation surface moved: re-take BOTH lane artifacts");

    let text = std::fs::read_to_string(fixture_dir().join("direct-lane.trust-ir.txt")).unwrap();
    assert!(!text.contains("requires"), "no contract obligation is born in the direct lane today");
    assert!(!text.contains("ensures"), "no contract obligation is born in the direct lane today");
    assert!(!text.contains("bounds"), "no slice bounds obligation is born in the direct lane today");

    // The lane's own self-declaration, read live from the producer source.
    let crate_module = std::fs::read_to_string(
        repo_root().join("crates/trust-thir-lower/src/crate_module.rs"),
    )
    .expect("crate_module.rs readable");
    assert!(
        crate_module.contains("structural-parity-only-v1"),
        "trust-thir-lower no longer declares structural-parity-only-v1: the direct lane's \
         obligation capability changed — re-take the artifacts and re-derive this pin"
    );
}

/// Pin 5 — the LO-edge triple, the one span form BOTH lanes can compute today,
/// AGREES across lanes wherever both mint an obligation — and is NOT injective:
/// add3's two no_overflow obligations share one LO triple in both lanes, and
/// contract_div_index's bounds row shares its LO with its div row. An anchor
/// needs the HI edge (or equivalent extent data), which only un-collapsed spans
/// carry.
#[test]
fn lo_triples_agree_across_lanes_but_do_not_separate_obligations() {
    let rows = mir_rows();
    let asserts = direct_asserts();
    // Cross-lane agreement, where the direct lane births the obligation at all.
    for (function, kind, tag) in [
        ("fixture::contract_div_index", "divzero", "div_nonzero"),
        ("fixture::add3", "overflow:add", "no_overflow"),
        ("fixture::macro_div", "divzero", "div_nonzero"),
    ] {
        let mir_lo: Vec<(u64, u64)> = rows
            .iter()
            .filter(|r| r.function == function && r.kind == kind)
            .map(|r| (r.span.0, r.span.1))
            .collect();
        let direct_lo: Vec<(u64, u64)> = asserts
            .iter()
            .filter(|a| function.ends_with(a.function.as_str()) && a.proof_tag == tag)
            .map(|a| (a.loc.1, a.loc.2))
            .collect();
        for lo in &direct_lo {
            assert!(mir_lo.contains(lo), "{function}: direct-lane LO {lo:?} matches a MIR-lane LO");
        }
    }
    // Non-injectivity, lane by lane.
    let add3_direct: Vec<(u64, u64, u64)> =
        asserts.iter().filter(|a| a.function == "add3").map(|a| a.loc).collect();
    assert_eq!(add3_direct[0], add3_direct[1], "direct lane: the two adds share one LO triple");
    let f1 = |kind: &str| {
        rows.iter()
            .find(|r| r.function == "fixture::contract_div_index" && r.kind == kind)
            .map(|r| (r.span.0, r.span.1))
            .expect("row present")
    };
    assert_eq!(f1("slice"), f1("divzero"), "MIR lane: bounds and div share one LO");
}

/// Pin 6 — the mint sites themselves, read live (span_normalization_parity
/// style): the safety mint is the carrier-index `format!("vc:{}:{}:{}", …)`
/// (three copies) and the contract mint indexes by CONTRACT position. If either
/// changes, the frozen artifacts above are stale evidence — re-take them.
#[test]
fn mint_sites_still_have_the_pinned_shape() {
    let api = std::fs::read_to_string(repo_root().join("crates/trust-mir-extract/src/verifier_api.rs"))
        .expect("verifier_api.rs readable");
    let vc_mints = api.matches(r#""vc:{}:{}:{}""#).count();
    assert_eq!(
        vc_mints, 3,
        "expected exactly the three carrier-index safety mint sites in verifier_api.rs \
         (verifier_vc_content_identity_with_source_digest_and_crate_name, \
         function_to_verifier_api_bundle_with_loop_feedback_candidates_and_crate_name, \
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
