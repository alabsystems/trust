// The strict-policy assumption-row table in `trust_types::assumption` must name what the
// compiler actually mints.
//
// `trust_types::assumption::strict_policy_publishes_assumption_row` is what the default
// `targo trust` gate (`GateLane::Strict`) uses to admit an `assumption:*` row as
// conditional evidence. Every other `assumption:*` row counts as a genuine unknown.
// The table restates labels the compiler mints in
// `compiler/rustc_mir_transform/src/trust_verify.rs`, some of them private `const`s
// there. If the compiler renames one, a strict row the table no longer recognizes
// fails closed: it counts as unknown, and an `#[trust::assume_total]` program stops
// passing `targo trust check`. That regression would surface only in a real crate
// run. This test surfaces it here instead.
//
// If this test fails, update the table and this pin together. A compiler label that
// moved is a table edit. A new strict-policy assumption row is a decision about what
// the default lane may pass: record it in the table's doc comment first.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use trust_types::assumption::{
    ASSUMED_TOTAL_ASSUMPTION_ROW_SOLVER, ASSUMED_TOTAL_ASSUMPTION_TAG,
    ASSUMED_TOTAL_CALLEE_BRIDGE_ROW_SOLVER, ASSUMED_TOTAL_CALLEE_FULL_VERIFICATION_ROW_SOLVER,
    ENTRY_REQUIRES_ASSUMPTION_ROW_SOLVER, ENTRY_REQUIRES_ASSUMPTION_TAG,
};

const TRUST_VERIFY: &str = "compiler/rustc_mir_transform/src/trust_verify.rs";
const BRIDGE_LOWER: &str = "crates/trust-ir-bridge/src/lower.rs";
const TERMINATION_UNMEASURED: &str =
    "compiler/rustc_mir_transform/src/trust_verify/termination_unmeasured.rs";
const SAFETY_COMMENT: &str =
    "compiler/rustc_mir_transform/src/trust_verify/safety_comment_assumption.rs";

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is <repo>/crates/trust-types.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").canonicalize().expect("repo root")
}

fn trust_verify_source() -> String {
    let path = repo_root().join(TRUST_VERIFY);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// The body of `fn <name>`, brace-matched from the first `{` after the signature.
fn fn_body(src: &str, name: &str) -> String {
    let needle = format!("fn {name}(");
    let start =
        src.find(&needle).unwrap_or_else(|| panic!("`fn {name}` is gone from {TRUST_VERIFY}"));
    let open = start + src[start..].find('{').expect("function body");
    let mut depth = 0usize;
    for (offset, byte) in src.as_bytes()[open..].iter().enumerate() {
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return src[open + 1..open + offset].to_string();
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced body for `fn {name}`")
}

fn assert_contains(haystack: &str, needle: &str, site: &str) {
    assert!(
        haystack.contains(needle),
        "{TRUST_VERIFY}: {site} no longer contains `{needle}`; the strict-policy row table in \
         trust_types::assumption must follow it"
    );
}

#[test]
fn the_definition_entry_row_is_spelled_as_the_table_says() {
    let src = trust_verify_source();
    assert_contains(
        &src,
        &format!(
            "const TRUST_ENTRY_ASSUMPTION_TRANSPORT_KIND: &str = \"assumption:{ENTRY_REQUIRES_ASSUMPTION_TAG}\";"
        ),
        "the definition-entry row kind",
    );
    assert_contains(
        &src,
        &format!(
            "const TRUST_ENTRY_ASSUMPTION_SOLVER: &str = \"{ENTRY_REQUIRES_ASSUMPTION_ROW_SOLVER}\";"
        ),
        "the definition-entry row solver",
    );
}

#[test]
fn the_assume_total_rows_are_spelled_as_the_table_says() {
    let src = trust_verify_source();
    // `#[trust::assume_total]` on the function itself: the skip tag and the solver
    // `record_skip_assumption` stamps outside a memory-safe demotion.
    assert_contains(
        &fn_body(&src, "skip_assumption_tag"),
        &format!("TrustVerifySkipReason::AssumedTotal => \"{ASSUMED_TOTAL_ASSUMPTION_TAG}\""),
        "`skip_assumption_tag`",
    );
    assert_contains(
        &fn_body(&src, "record_skip_assumption"),
        &format!(
            "| TrustVerifySkipReason::AssumedTotal => \"{ASSUMED_TOTAL_ASSUMPTION_ROW_SOLVER}\""
        ),
        "`record_skip_assumption`",
    );
    // ... and the skip is recorded, not aborted, under strict policy.
    let strict_skip = fn_body(&src, "skip_is_full_verification_failure");
    assert_contains(
        &strict_skip,
        "if matches!(reason, TrustVerifySkipReason::AssumedTotal) {\n            return false;",
        "`skip_is_full_verification_failure`",
    );
    // A call to an `#[trust::assume_total]` wrapper, both producers.
    assert_contains(
        &src,
        &format!(
            "const TRUST_ASSUMED_TOTAL_SOLVER: &str = \"{ASSUMED_TOTAL_CALLEE_FULL_VERIFICATION_ROW_SOLVER}\";"
        ),
        "the full-verification assumed-total-callee solver",
    );
    let bridge = fn_body(&src, "demote_assumed_total_callee_transport_rows");
    assert_contains(
        &bridge,
        "trust_types::assumption::ASSUMED_TOTAL_CALLEE_ASSUMPTION_TAG",
        "`demote_assumed_total_callee_transport_rows`",
    );
    assert_contains(
        &bridge,
        &format!("\"{ASSUMED_TOTAL_CALLEE_BRIDGE_ROW_SOLVER}\""),
        "`demote_assumed_total_callee_transport_rows`",
    );
}

#[test]
fn the_fmt_format_leg_is_spelled_as_the_table_says() {
    let src = trust_verify_source();
    // The one extern-call leg the strict policy demotes: the `fmt::format` callee,
    // stamped with the memory-safe row source.
    let leg = fn_body(&src, "demote_fmt_format_extern_call_transport_rows");
    assert_contains(&leg, "trust_types::assumption::EXTERN_CALL_ASSUMPTION_TAG", "the b59 leg");
    assert_contains(
        &leg,
        "trust_types::assumption::MEMORY_SAFE_ASSUMPTION_ROW_SOURCE",
        "the b59 leg",
    );
    assert_contains(
        &fn_body(&src, "transport_row_is_unproved_fmt_format_extern_call"),
        "callee.ends_with(\"::fmt::format\")",
        "`transport_row_is_unproved_fmt_format_extern_call`",
    );
    assert!(trust_types::assumption::is_fmt_format_dispatch_callee("alloc::fmt::format"));
    // The strict decision may demote the `fmt::format` leg and nothing else.
    let decision = fn_body(&src, "default_lane_demotion_decision");
    assert_contains(
        &decision,
        "if strict_enforcement {\n        return fmt_format_demotion_only(fmt_format_demotable);\n    }",
        "`default_lane_demotion_decision`",
    );
}

/// The table admits the b59 row by the callee it reads out of the row's
/// DESCRIPTION, so the description has to reach targo in the shape the table
/// parses. Three producers write it: the bridge mints the obligation text, the
/// compiler keeps what follows the marker, and `transport_assumption_row` prefixes
/// "unverified assumption: ". This pins all three and composes them. If one moves,
/// a legitimate strict row would be counted unknown and every crate that uses
/// `format!` would stop passing `targo trust check`.
#[test]
fn the_fmt_format_row_description_reaches_the_table_in_the_shape_it_parses() {
    use trust_types::assumption::{
        EXTERN_CALL_ASSUMPTION_PREFIX, MEMORY_SAFE_ASSUMPTION_ROW_SOURCE,
        strict_policy_publishes_assumption_row,
    };

    let bridge_path = repo_root().join(BRIDGE_LOWER);
    let bridge = std::fs::read_to_string(&bridge_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", bridge_path.display()));
    assert!(
        bridge.contains(
            "\"{}extern print/format/write dispatch `{callee}` runs a user Display/Debug impl \
             that may panic\""
        ),
        "{BRIDGE_LOWER}: the extern-call obligation text moved; the strict-policy row table in \
         trust_types::assumption reads the callee out of it and must follow it"
    );
    let src = trust_verify_source();
    assert_contains(
        &fn_body(&src, "demote_fmt_format_extern_call_transport_rows"),
        ".split(trust_types::assumption::EXTERN_CALL_ASSUMPTION_PREFIX)\n                    .nth(1)",
        "the b59 leg's detail",
    );
    assert_contains(
        &fn_body(&src, "transport_assumption_row"),
        "description: format!(\"unverified assumption: {detail}\")",
        "`transport_assumption_row`",
    );
    // The compiler picks the callee from the same first backtick pair.
    assert_contains(
        &fn_body(&src, "extern_call_row_callee"),
        "let (_, after) = description.split_once('`')?;\n    let (callee, _) = after.split_once('`')?;",
        "`extern_call_row_callee`",
    );

    for (callee, admitted) in
        [("alloc::fmt::format", true), ("std::io::_print", false), ("std::io::_eprint", false)]
    {
        // The row as the bridge mints it and `VcKind::Assertion` renders it ...
        let obligation = format!(
            "assertion: {EXTERN_CALL_ASSUMPTION_PREFIX}extern print/format/write dispatch \
             `{callee}` runs a user Display/Debug impl that may panic"
        );
        // ... and as the b59 demotion rewrites it.
        let detail = obligation
            .split(EXTERN_CALL_ASSUMPTION_PREFIX)
            .nth(1)
            .map(str::trim)
            .expect("the marker is in the obligation text");
        let description = format!("unverified assumption: {detail}");
        assert_eq!(
            strict_policy_publishes_assumption_row(
                "assumption:extern-call",
                MEMORY_SAFE_ASSUMPTION_ROW_SOURCE,
                &description,
            ),
            admitted,
            "{callee}: {description}"
        );
    }
}

/// D9 (ruled 2026-09-27): the `assumption:termination-unmeasured` charge. The table
/// admits it by (kind, solver); the compiler seam must mint it from the SAME
/// constants, publish it `skipped`, and abort only under `certify`. If the seam
/// stopped using the constants, a renamed label would count as a genuine unknown on
/// the default lane and every structurally recursive function would stop passing
/// `targo trust check`.
#[test]
fn the_termination_unmeasured_row_is_minted_as_the_table_says() {
    use trust_types::assumption::{
        TERMINATION_UNMEASURED_ASSUMPTION_TAG, TERMINATION_UNMEASURED_ROW_SOLVER,
        strict_policy_publishes_assumption_row,
    };

    let seam_path = repo_root().join(TERMINATION_UNMEASURED);
    let seam = std::fs::read_to_string(&seam_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", seam_path.display()));
    let row = fn_body(&seam, "termination_unmeasured_row");
    for needle in [
        "kind: termination_unmeasured_row_kind()",
        "solver: TERMINATION_UNMEASURED_ROW_SOLVER.to_string()",
        "outcome: Outcome::Skipped",
        "description: format!(\"unverified assumption: {}\", charge_detail(func_path, kind))",
    ] {
        assert!(
            row.contains(needle),
            "{TERMINATION_UNMEASURED}: `termination_unmeasured_row` no longer contains `{needle}`; \
             the strict-policy row table in trust_types::assumption must follow it"
        );
    }
    assert!(
        fn_body(&seam, "termination_unmeasured_row_kind")
            .contains("format!(\"assumption:{TERMINATION_UNMEASURED_ASSUMPTION_TAG}\")"),
        "{TERMINATION_UNMEASURED}: the row kind moved off the shared tag"
    );
    // The strict compiler publishes the row and aborts only under `certify`. (`fn_body`
    // cannot take `publish_body_verification_outcome`: its signature is generic.)
    let publish = trust_verify_source();
    for needle in [
        "termination_unmeasured::termination_unmeasured_charge(",
        concat!(
            "if matches!(policy.policy, rustc_session::config::TrustPolicy::Certify)\n",
            "        && let Some(charge) = &termination_unmeasured_charge\n",
            "    {\n",
            "        termination_unmeasured::abort_on_termination_unmeasured(",
        ),
    ] {
        assert_contains(&publish, needle, "`publish_body_verification_outcome`");
    }
    assert!(strict_policy_publishes_assumption_row(
        &format!("assumption:{TERMINATION_UNMEASURED_ASSUMPTION_TAG}"),
        TERMINATION_UNMEASURED_ROW_SOLVER,
        "unverified assumption: termination of `c::f`: this self call binds no `decreases` measure",
    ));
}

/// SAFETY-ASSUME-1 (ruled 2026-10-17): the `assumption:safety-comment` charge row is
/// minted in the table's exact (kind, solver) pair, `skipped`, and the strict compiler
/// publishes it and aborts only under `certify`.
#[test]
fn the_safety_comment_row_is_minted_as_the_table_says() {
    use trust_types::assumption::{
        SAFETY_COMMENT_ASSUMPTION_TAG, SAFETY_COMMENT_ROW_SOLVER,
        strict_policy_publishes_assumption_row,
    };

    let seam_path = repo_root().join(SAFETY_COMMENT);
    let seam = std::fs::read_to_string(&seam_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", seam_path.display()));
    let row = fn_body(&seam, "safety_comment_row");
    for needle in [
        "kind: safety_comment_row_kind()",
        "solver: SAFETY_COMMENT_ROW_SOLVER.to_string()",
        "outcome: Outcome::Skipped",
        "\"unverified assumption: {}\",",
    ] {
        assert!(
            row.contains(needle),
            "{SAFETY_COMMENT}: `safety_comment_row` no longer contains `{needle}`; the \
             strict-policy row table in trust_types::assumption must follow it"
        );
    }
    assert!(
        fn_body(&seam, "safety_comment_row_kind")
            .contains("format!(\"assumption:{SAFETY_COMMENT_ASSUMPTION_TAG}\")"),
        "{SAFETY_COMMENT}: the row kind moved off the shared tag"
    );
    let publish = trust_verify_source();
    for needle in [
        "safety_comment_assumption::safety_comment_charge(",
        concat!(
            "if matches!(policy.policy, rustc_session::config::TrustPolicy::Certify)\n",
            "        && let Some(charge) = &safety_comment_charge\n",
            "    {\n",
            "        safety_comment_assumption::abort_on_safety_comment_assumptions(",
        ),
    ] {
        assert_contains(&publish, needle, "`publish_body_verification_outcome`");
    }
    assert!(strict_policy_publishes_assumption_row(
        &format!("assumption:{SAFETY_COMMENT_ASSUMPTION_TAG}"),
        SAFETY_COMMENT_ROW_SOLVER,
        "unverified assumption: the unsafe block at f.rs:3:5 in `c::f` is declared sound",
    ));
}
