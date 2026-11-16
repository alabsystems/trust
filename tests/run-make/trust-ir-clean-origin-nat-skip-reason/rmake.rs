//! WS5.14 (F-095, stale-text half): the recorded skip reason for a `Nat`
//! recursion names the REAL blockers, at the real compiler surface.
//!
//! `crates/trust-clean-ir/tests/planner_skip_reason.rs` pins the text against
//! real planned Clean declarations. This fixture pins the other half: that the
//! text is what the compiler actually WRITES into
//! `clean_origin.skipped[].reason` of the coverage sidecar — the field
//! `scripts/trust_clean_corpus_scorecard.py` reads, and the string the proof
//! program's `a.lean.nat_structural.carried` / `a.lean.nat_wf.carried` ratchets
//! are signed on.
//!
//! Pins:
//!  * both recursion shapes carry the SHAPE NOTE, and it names all four live
//!    blockers (the minter with no caller, the join's two handle refusals, the
//!    missing callee-remap seam, and the by-value/boxed-handle Rust boundary),
//!    and says the seam's own edge type check (IR-5's `repoint_edges`, typed
//!    for unsigned declarations too since 3b30328c07) is NOT a blocker;
//!  * neither carries the three claims that had gone stale — a `Ty::Ptr`
//!    carrier (it is the v43 `Ty::Handle` now), "those four callees" (the
//!    pinned row is five, including the release entry), and an ARITY-ALONE
//!    edge repoint (the seam type-checks it now);
//!  * NEGATIVE TWIN: `natId` is the same carrier refused at the same position
//!    by the same walk, and being a projection rather than a recursion it keeps
//!    the PLAIN text — so the note is caused by the shape, not by the `Nat`;
//!  * the rows are still SKIPS. This increment changes text only: no row moved
//!    tier, and nothing became emitted.

use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// Every blocker the SHAPE NOTE must name. Kept as one list so a partial
/// rewrite cannot quietly drop one, exactly as the crates-lane test does.
const BLOCKERS: &[&str] = &[
    "declare_pinned_nat_runtime",
    "NO caller in the compiler",
    "clean_origin_join",
    "remap_general_ty",
    "remap_ty",
    "HandleForeignDeclaration",
    "append_clean_origin",
    "callee-remap seam",
    "repoint_edges",
    "NOT a blocker",
    "ty_link_verdict",
    "type_unchecked",
    "BY VALUE",
    "BOXED HANDLE",
    "five entry points",
];

/// The claims the old text made that are FALSE at this tree. Absence is the
/// assertion: a rewrite that kept either would be the same defect again.
const STALE: &[&str] = &["Ty::Ptr", "those four callees are not present", "ARITY ALONE"];

fn main() {
    let dir = Path::new("emit-on");
    rfs::create_dir(&dir);
    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&dir)
        .arg("-Ztrust-verify=on")
        // Bootstrap may deauthorize its own nested compiler processes through
        // this inherited override; the recipe's explicit flag must win.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();

    let coverage = rfs::read_to_string(dir.join("foo.trust-ir.coverage.json"));
    let json: serde_json::Value =
        serde_json::from_str(&coverage).expect("coverage sidecar must be valid JSON");
    assert!(
        coverage.contains("\"recorded\": true"),
        "clean_origin section must record under verification:\n{coverage}"
    );
    let skipped =
        json["clean_origin"]["skipped"].as_array().expect("clean_origin.skipped array").clone();

    let row = |name: &str| -> serde_json::Value {
        skipped
            .iter()
            .find(|row| row["clean_name"] == name)
            .unwrap_or_else(|| panic!("`{name}` must have one SKIPPED row:\n{coverage}"))
            .clone()
    };
    let reason_of = |row: &serde_json::Value| -> String {
        row["reason"].as_str().expect("a skip row carries a string reason").to_string()
    };

    // ── positive: both recursion shapes ──────────────────────────────────
    for (name, shape) in
        [("tozero", "structural-nat-rec"), ("countdownSum", "well-founded-nat-rec")]
    {
        let row = row(name);
        assert_eq!(row["shape"], shape, "the probe must really be that shape: {row}");
        let reason = reason_of(&row);
        assert!(
            reason.starts_with("Clean type Nat at argument 0 has no TrustIR type ON THIS WALK."),
            "the carrier refusal is re-worded and still first: {reason}"
        );
        assert!(reason.contains("SHAPE NOTE"), "{name} must carry the note: {reason}");
        assert!(
            reason.contains(r#"Ty::Handle(\"Nat\", \"trust_bignum::Nat\")"#)
                || reason.contains(r#"Ty::Handle("Nat", "trust_bignum::Nat")"#),
            "the note must name the v43 handle carrier: {reason}"
        );
        for needle in BLOCKERS {
            assert!(reason.contains(needle), "{name}'s note must name `{needle}`: {reason}");
        }
        for stale in STALE {
            assert!(!reason.contains(stale), "{name}'s note still carries stale `{stale}`");
        }
        assert!(reason.contains("Options:"), "a refusal carries its next step: {reason}");
    }

    // ── negative twin: same carrier, same refusal, different shape ────────
    let nat_id = row("natId");
    assert_eq!(nat_id["shape"], "projection", "the twin must be a non-recursion shape: {nat_id}");
    let twin = reason_of(&nat_id);
    assert!(
        twin.starts_with("Clean type Nat at argument 0 has no TrustIR type ON THIS WALK."),
        "the twin must reach the SAME refusal, or it measures nothing: {twin}"
    );
    assert!(!twin.contains("SHAPE NOTE"), "a projection gets no recursion note: {twin}");
    for needle in BLOCKERS {
        assert!(!twin.contains(needle), "the twin must not carry `{needle}`: {twin}");
    }

    // ── this increment changed TEXT only ─────────────────────────────────
    let emitted = json["clean_origin"]["emitted"].as_array().expect("clean_origin.emitted array");
    for name in ["tozero", "countdownSum", "natId"] {
        assert!(
            !emitted.iter().any(|row| row["clean_name"] == name),
            "`{name}` must still be a SKIP, not an emitted row — WS5.14 is diagnostics only"
        );
    }
}
