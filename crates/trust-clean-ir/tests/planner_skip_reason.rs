// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! WS5.14 (F-095, stale-text half): the Nat skip text and the carrier refusal
//! stop misnaming the blocker.
//!
//! THE HOLE. Every `Nat -> Nat` recursion the Clean-origin planner meets is
//! recorded as a SKIP, and the reason it records is read by humans and by the
//! corpus scorecard. Two of those texts had gone stale, and a reason that
//! misnames the blocker is a v7/D3 defect:
//!
//! * `planner_skip_reason`'s SHAPE NOTE said the blocker was "those four
//!   callees are not present in the crate Module" and "the emitted `Ty::Ptr`
//!   carrier is opaque". Measured at this tree: the emitter calls FIVE pinned
//!   entry points ([`NAT_RUNTIME_ROLES`], including the release entry
//!   [`NAT_RELEASE_ROLE`]), [`declare_pinned_nat_runtime`] already writes
//!   exactly those five from the validator's own pin row (it simply has no
//!   caller in the compiler; the row itself is wider — nineteen shims at the
//!   trust-ir `7b9146ba` gitlink), and the carrier has been the nominal opaque
//!   handle [`nat_handle_ty`] since trust-ir v43 — never a `Ty::Ptr`.
//! * [`CleanIrRefusal::CarrierHasNoTrustIrType`]'s Display said "TrustIR
//!   carries fixed-width machine integers and `bool`; `Nat` and `Int` are
//!   unbounded", which reads as "`Nat` has no TrustIR spelling". It has one.
//!   What it does not have on THIS walk is a runtime to own the arithmetic.
//!
//! THE RULE. Same verdict, same row, same tier — only the text changes. The
//! note names the four live blockers, each re-measured at this tree (a fifth,
//! the arity-only edge repoint, was retired by IR-5's typed seam and the note
//! now says it is NOT a blocker), and the
//! carrier refusal distinguishes the three cases it lumped together (`Nat`
//! carriable at the v43 handle with a runtime; `Int` no row at all; `USize`
//! target-dependent).
//!
//! WHERE THE TEXT LIVES. `planner_skip_reason` moved from
//! `rustc_mir_transform::clean_origin_ir` into this crate, beside the refusal
//! it annotates, so it is measurable here against REAL planned Clean
//! declarations instead of only through a stage-1 compile. It now matches on
//! the SHAPE VARIANT rather than on the compiler's rendered `shape_tag`
//! string, so renaming a coverage tag cannot silently drop the note.

use clean_kernel::Environment;
use trust_clean_carrier::CleanType;
use trust_clean_ir::{
    CleanIrRefusal, NAT_RELEASE_ROLE, NAT_RUNTIME_ROLES, planner_skip_reason, trust_ir_func_ty,
};
use trust_clean_origin::emit::CleanOriginShape;
use trust_clean_origin::plan_clean_origin_body;

// ── the sources ───────────────────────────────────────────────────────────

/// The proof program's `p16_lean_nat_structural` probe: the structural
/// recursion whose skip row is ratchet `a.lean.nat_structural.carried`.
const TOZERO: &str = "def tozero : Nat -> Nat\n  | 0 => 0\n  | n + 1 => tozero n";

/// The proof program's well-founded probe, and the source
/// `tests/nat_recursion.rs` already pins as the one spelling the planner admits
/// as a `WellFoundedNatRec`. Its skip row is ratchet `a.lean.nat_wf.carried`.
const COUNTDOWN_SUM: &str = "def countdownSum (n : Nat) : Nat := \
                             if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                             termination_by n";

/// THE NEGATIVE TWIN. The same `Nat` carrier, refused at the same position by
/// the same signature walk, differing from the two above by exactly one thing:
/// the SHAPE. A projection is not a recursion, so the note must not appear.
const NAT_ID: &str = "def natId (n : Nat) : Nat := n";

/// The roadmap's named twin. It never reaches this path at all — see
/// [`mixed_add_is_refused_before_the_skip_path_exists`].
const MIXED_ADD: &str = "def mixedAdd (a : Nat) (b : UInt64) : UInt64 := b + b";

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// Reproduce the planner lane's recording path for one declaration: plan it,
/// walk its signature WITHOUT a runtime (which is what the compiler's recording
/// seam does), and annotate the refusal at the plan's own shape.
///
/// Returns the shape and the recorded reason, so every assertion below is over
/// the string the coverage row would actually carry.
fn skip_row(decl: &str, name: &str) -> (CleanOriginShape, CleanIrRefusal, String) {
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, name)
        .unwrap_or_else(|e| panic!("`{name}` must plan (did the fragment boundary move?): {e:?}"));
    let refusal = trust_ir_func_ty(plan.signature())
        .expect_err("a `Nat` position must refuse the runtime-less signature walk");
    let reason = planner_skip_reason(plan.shape(), &refusal);
    (plan.shape().clone(), refusal, reason)
}

/// Every needle the SHAPE NOTE must carry, each one a blocker re-measured at
/// this tree. Asserted as a set so a partial rewrite cannot quietly drop one.
fn assert_names_the_real_blockers(reason: &str) {
    // (1) the minter exists and has no caller.
    assert!(
        reason.contains("declare_pinned_nat_runtime"),
        "the note must name the minter that already exists: {reason}"
    );
    assert!(
        reason.contains("NO caller in the compiler"),
        "the note must say WHY the minter does not help yet: {reason}"
    );
    // (2) the join refuses the handle in both general remap lanes.
    assert!(
        reason.contains("clean_origin_join"),
        "the note must name the join that refuses the handle: {reason}"
    );
    assert!(
        reason.contains("remap_general_ty") && reason.contains("remap_ty"),
        "BOTH general remap lanes refuse it, and the signature lane runs first: {reason}"
    );
    assert!(
        reason.contains("HandleForeignDeclaration"),
        "the note must name the validation error an admitted handle would earn: {reason}"
    );
    // (3) the append path still has no callee-remap seam.
    assert!(
        reason.contains("append_clean_origin") && reason.contains("callee-remap seam"),
        "the note must name the missing seam: {reason}"
    );
    // (4) the Rust-side boundary, which the three above do not fix.
    assert!(
        reason.contains("BY VALUE") && reason.contains("BOXED HANDLE"),
        "the note must name the by-value/handle boundary mismatch: {reason}"
    );
    // NOT a blocker (landing review, 2026-09-28): IR-5's `repoint_edges` TYPE-checks a
    // re-pointed edge, unsigned declaration or not (`ty_link_verdict`, 3b30328c07). The
    // note must say so rather than go on naming the arity-only guard it replaced.
    assert!(
        reason.contains("NOT a blocker")
            && reason.contains("repoint_edges")
            && reason.contains("TYPES")
            && reason.contains("ty_link_verdict")
            && reason.contains("type_unchecked"),
        "the note must say the seam's own type check is not the blocker, and name it: {reason}"
    );

    // The carrier, and the pinned row, as they actually are at this tree.
    assert!(
        reason.contains(r#"Ty::Handle("Nat", "trust_bignum::Nat")"#),
        "the note must name the v43 handle carrier: {reason}"
    );
    assert!(
        reason.contains("five entry points it calls"),
        "five called roles, not four — and not \"the row's five\": the pin row is wider: {reason}"
    );
    assert!(
        !reason.contains("PINNED row's five"),
        "the pin row is nineteen shims at this tree; only the CALLED roles are five: {reason}"
    );
    for role in NAT_RUNTIME_ROLES {
        assert!(reason.contains(role), "the note must name the pinned role `{role}`: {reason}");
    }
    assert!(
        reason.contains(NAT_RELEASE_ROLE) && reason.contains("RELEASE entry"),
        "the release entry is the one the old text dropped: {reason}"
    );

    // The row is still recorded, and the note still carries options (v7/D3).
    assert!(reason.contains("tier `general`"), "the row is not unrecorded: {reason}");
    assert!(reason.contains("Options:"), "a refusal must carry its next step: {reason}");
}

/// The claims the old text made that are FALSE at this tree. Absence is the
/// assertion — a rewrite that kept either would be the same defect again.
fn assert_stale_claims_are_gone(reason: &str) {
    assert!(
        !reason.contains("Ty::Ptr"),
        "the carrier has not been `Ty::Ptr` since trust-ir v43: {reason}"
    );
    assert!(
        !reason.contains("those four callees are not present"),
        "the emitter calls five pinned entry points and the minter writes them: {reason}"
    );
    assert!(
        !reason.contains("ARITY ALONE") && !reason.contains("type-check the re-pointed"),
        "IR-5's seam has type-checked unsigned declarations' edges since 3b30328c07; an \
         arity-only blocker, or an option to add that check, is the stale claim again: {reason}"
    );
}

// ── positive ──────────────────────────────────────────────────────────────

/// `tozero` — a real structurally recursive Clean definition, planned through a
/// real island session — records a skip whose note names the real blockers.
#[test]
fn structural_nat_rec_skip_text_names_the_real_blockers() {
    let (shape, refusal, reason) = skip_row(TOZERO, "tozero");
    assert!(
        matches!(shape, CleanOriginShape::StructuralNatRec { .. }),
        "the note is keyed on the shape VARIANT, so the probe must really be one: {shape:?}"
    );
    assert!(
        matches!(
            refusal,
            CleanIrRefusal::CarrierHasNoTrustIrType { position: Some(0), clean: CleanType::Nat }
        ),
        "the first refusal is the carrier one at argument 0 — the whole reason the \
         note exists: {refusal:?}"
    );
    assert_names_the_real_blockers(&reason);
    assert_stale_claims_are_gone(&reason);
}

/// `countdownSum` — the well-founded twin of the above — gets the same note.
/// Two shapes, one text: the note is a property of the recursion FAMILY.
#[test]
fn well_founded_nat_rec_skip_text_names_the_real_blockers() {
    let (shape, _, reason) = skip_row(COUNTDOWN_SUM, "countdownSum");
    assert!(
        matches!(shape, CleanOriginShape::WellFoundedNatRec { .. }),
        "the well-founded probe must really plan as one: {shape:?}"
    );
    assert_names_the_real_blockers(&reason);
    assert_stale_claims_are_gone(&reason);

    let (_, _, structural) = skip_row(TOZERO, "tozero");
    assert_eq!(
        reason, structural,
        "both recursion shapes are `Nat -> Nat` in every position by plan construction, \
         so one text serves both — a divergence here would mean the arm had split"
    );
}

// ── the proof program's GAP rows, ported by name ───────────────────────────
//
// The two rows this increment re-signs are pinned TWICE: here, named after the
// rows, against the planner-lane text itself; and end to end in WS5.1's producer
// ratchets (`tests/two-language-programs/ir-ta16_lean_nat_structural/` and
// `ir-ta17_lean_nat_wf/` `expected.json`, whose GAP signature is the first 200
// squashed characters of the SAME reason as the compiler's coverage sidecar
// records it). Each asserts the CURRENT WRONG OUTCOME exactly (§2.4.1): the
// declaration is NOT carried as a planner-emitted TrustIR function, and the
// reason it is not is the named carrier refusal plus the updated note. They flip
// to PASS in WS5.15.

/// Ratchet `a.lean.nat_structural.carried` — still GAP, at the updated
/// signature. `tozero` is skipped by the TrustIR Clean-origin producer, and the
/// recorded detail now opens with the re-worded carrier refusal.
#[test]
fn a_lean_nat_structural_carried() {
    let (_, _, reason) = skip_row(TOZERO, "tozero");
    assert!(
        reason.starts_with("Clean type Nat at argument 0 has no TrustIR type ON THIS WALK."),
        "the ratchet's detail prefix is re-signed by this increment: {reason}"
    );
    assert!(
        !reason.starts_with(
            "Clean type Nat at argument 0 has no TrustIR type. TrustIR carries fixed-width"
        ),
        "the old signature must be gone, not merely widened"
    );
}

/// Ratchet `a.lean.nat_wf.carried` — still GAP, at the updated signature.
#[test]
fn a_lean_nat_wf_carried() {
    let (_, _, reason) = skip_row(COUNTDOWN_SUM, "countdownSum");
    assert!(
        reason.starts_with("Clean type Nat at argument 0 has no TrustIR type ON THIS WALK."),
        "the ratchet's detail prefix is re-signed by this increment: {reason}"
    );
}

/// The GAP signature `scripts/two_language_producer_ratchets.py` computes for a skipped
/// Lean def: `carried:<def>:skipped:` + the first 200 characters of the reason with every
/// whitespace run squashed to one space (`squash(reason)[:200]`).
fn judge_signature(def: &str, reason: &str) -> String {
    let squashed = reason.split_whitespace().collect::<Vec<_>>().join(" ");
    format!("carried:{def}:skipped:{}", squashed.chars().take(200).collect::<String>())
}

/// The `signature` pinned for ratchet `id` in a producer-ratchet row's `expected.json`.
/// A minimal reader (this crate has no JSON dependency, and adding one would move the
/// lockfile): the first `"signature"` string after the ratchet's key, JSON-unescaped.
fn pinned_signature(row: &str, id: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/two-language-programs")
        .join(row)
        .join("expected.json");
    let doc = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: the WS5.1 pin must exist: {e}", path.display()));
    let at = doc.find(&format!("\"{id}\"")).unwrap_or_else(|| panic!("{row}: no pin `{id}`"));
    let rest = &doc[at..];
    let sig =
        rest.find("\"signature\"").unwrap_or_else(|| panic!("{row}: `{id}` has no signature"));
    let rest = rest[sig + "\"signature\"".len()..].trim_start();
    let rest = rest.strip_prefix(':').expect("`:` after the key").trim_start();
    let mut chars = rest.strip_prefix('"').expect("a JSON string").chars();
    let mut out = String::new();
    loop {
        match chars.next().expect("an unterminated JSON string") {
            '"' => return out,
            '\\' => match chars.next().expect("an escape") {
                'u' => {
                    let hex: String = chars.by_ref().take(4).collect();
                    let code = u32::from_str_radix(&hex, 16).expect("a \\u escape");
                    out.push(char::from_u32(code).expect("a scalar value"));
                }
                'n' => out.push('\n'),
                't' => out.push('\t'),
                'r' => out.push('\r'),
                other => out.push(other),
            },
            c => out.push(c),
        }
    }
}

/// The END-TO-END pins of the two rows above are WS5.1's producer ratchets, and they are
/// signed by THIS text: the judge reads `clean_origin.skipped[].reason` from the compiler's
/// coverage sidecar and pins the first 200 squashed characters. WS5.14 was written before
/// WS5.1 landed, re-worded the reason, and left both pins on the OLD text — the lane's e2e
/// leg would have failed both rows with "GAP changed its named signature". This keeps the
/// planner text and the e2e pins from drifting apart again without a stage-1 build.
#[test]
fn the_producer_ratchet_pins_carry_this_signature() {
    for (source, def, row, id) in [
        (TOZERO, "tozero", "ir-ta16_lean_nat_structural", "a.lean.nat_structural.carried"),
        (COUNTDOWN_SUM, "countdownSum", "ir-ta17_lean_nat_wf", "a.lean.nat_wf.carried"),
    ] {
        let (_, _, reason) = skip_row(source, def);
        assert_eq!(
            pinned_signature(row, id),
            judge_signature(def, &reason),
            "{row}/expected.json `{id}` must pin the signature the judge computes from the \
             planner lane's CURRENT reason; update the pin in the same commit as the text"
        );
    }
}

// ── negative twin ─────────────────────────────────────────────────────────

/// THE TWIN. `natId` is the same `Nat` carrier, the same refusal variant, the
/// same argument position, refused by the same signature walk — and it is a
/// `Projection`, not a recursion. It keeps the PLAIN carrier text, with no
/// shape note. One mutation (the shape), one difference in outcome.
#[test]
fn a_projection_at_the_same_carrier_keeps_the_plain_text() {
    let (shape, refusal, reason) = skip_row(NAT_ID, "natId");
    assert!(
        matches!(shape, CleanOriginShape::Projection { .. }),
        "the twin must be a non-recursion shape: {shape:?}"
    );
    assert!(
        matches!(
            refusal,
            CleanIrRefusal::CarrierHasNoTrustIrType { position: Some(0), clean: CleanType::Nat }
        ),
        "the twin must reach the SAME refusal — otherwise it measures nothing: {refusal:?}"
    );
    assert_eq!(reason, refusal.to_string(), "a non-recursion shape is annotated with nothing");
    assert!(!reason.contains("SHAPE NOTE"), "no note at a projection: {reason}");
    assert!(!reason.contains("declare_pinned_nat_runtime"), "{reason}");
    assert!(!reason.contains("repoint_edges"), "{reason}");
}

/// The roadmap named `mixedAdd` as the twin. MEASURED: it cannot be one,
/// because it never reaches this path — `check_arith_signature` refuses it at
/// PLAN time, before a `CleanOriginPlan` exists to carry a shape. Recorded
/// rather than silently substituted, because "the twin is somewhere else" is
/// itself the finding about where the `Nat` refusals live.
#[test]
fn mixed_add_is_refused_before_the_skip_path_exists() {
    let env = env_with(MIXED_ADD);
    let Err(refusal) = plan_clean_origin_body(&env, "mixedAdd") else {
        panic!("a `Nat` in ANY arithmetic signature position is refused at plan time");
    };
    let text = format!("{refusal:?}");
    assert!(
        text.contains("BignumNat"),
        "the plan-time refusal names the bignum carrier it refused: {text}"
    );
}

// ── mutation / adversarial controls ───────────────────────────────────────

/// THE MUTATION CONTROL. Drop the shape arm and the positive must fail: every
/// needle the positive asserts is absent from the bare refusal, so the note —
/// and only the note — can be what satisfies it. Equivalently, the arm is
/// load-bearing rather than decorative.
#[test]
fn the_note_and_not_the_refusal_is_what_carries_the_blockers() {
    let (_, refusal, reason) = skip_row(TOZERO, "tozero");
    let bare = refusal.to_string();

    for needle in [
        "SHAPE NOTE",
        "declare_pinned_nat_runtime",
        "clean_origin_join",
        "append_clean_origin",
        "repoint_edges",
        "HandleForeignDeclaration",
        "five entry points",
    ] {
        assert!(reason.contains(needle), "the annotated reason carries `{needle}`");
        assert!(
            !bare.contains(needle),
            "dropping the shape arm would lose `{needle}` — so the arm is what earns it: {bare}"
        );
    }

    // And the note APPENDS: the verdict the row records is unchanged, so this
    // increment cannot have widened or narrowed what is refused.
    assert!(
        reason.starts_with(&bare),
        "the recorded reason is the refusal verbatim plus a note, never a replacement"
    );
    assert!(
        reason[bare.len()..].starts_with("\n\nSHAPE NOTE:"),
        "the note is a labelled suffix, so a reader can tell the two apart"
    );
}

/// The arm is keyed on the shape VARIANT, so it cannot over-refuse by matching
/// a string: a shape whose rendered tag merely mentions recursion gets nothing,
/// and every non-recursion variant this crate emits keeps the plain text.
#[test]
fn only_the_two_recursion_variants_are_annotated() {
    let refusal =
        CleanIrRefusal::CarrierHasNoTrustIrType { position: Some(0), clean: CleanType::Nat };
    let bare = refusal.to_string();
    for shape in [
        CleanOriginShape::Projection { projected: 0 },
        CleanOriginShape::InductiveProjection { projected: 0 },
    ] {
        assert_eq!(
            planner_skip_reason(&shape, &refusal),
            bare,
            "{shape:?} must not be annotated with a recursion note"
        );
    }
}

// ── the carrier refusal's own text ────────────────────────────────────────

/// The Display of [`CleanIrRefusal::CarrierHasNoTrustIrType`] distinguishes the
/// three cases it used to lump together, and names the v43 carrier for the one
/// that HAS one.
#[test]
fn the_carrier_refusal_names_the_v43_handle_and_separates_int_from_usize() {
    let text = CleanIrRefusal::CarrierHasNoTrustIrType { position: Some(0), clean: CleanType::Nat }
        .to_string();

    assert!(
        text.contains(r#"Ty::Handle("Nat", "trust_bignum::Nat")"#),
        "the v43 carrier must be named: {text}"
    );
    assert!(
        text.contains("trust-ir v43") && text.contains("TRANSPORT only"),
        "and named as what it is — transport, not arithmetic: {text}"
    );
    assert!(
        text.contains("this walk was given none"),
        "the refusal must say what is actually missing (a runtime), not that `Nat` \
         has no spelling: {text}"
    );
    assert!(
        text.contains("`Int` has NO row at all"),
        "`Int` is a different story from `Nat` now: {text}"
    );
    assert!(text.contains("`USize` is target-dependent"), "and `USize` is a third: {text}");
    assert!(
        text.contains("_with_nat"),
        "the first option must be the one that works for `Nat`: {text}"
    );

    // The claim the old text made, which read as "`Nat` has no TrustIR type".
    assert!(
        !text.contains("`Nat` and `Int` are unbounded"),
        "the lumped-together sentence is gone: {text}"
    );

    // NOT weakened: the machine-width and proof-only options survive, because
    // for a non-machine `UInt`/`BitVec` width they are still the whole answer.
    let wide =
        CleanIrRefusal::CarrierHasNoTrustIrType { position: None, clean: CleanType::BitVec(128) }
            .to_string();
    assert!(wide.contains("`BitVec w`"), "{wide}");
    assert!(wide.contains("proof-only"), "{wide}");
    assert!(wide.contains("the result"), "the position is still named: {wide}");
}
