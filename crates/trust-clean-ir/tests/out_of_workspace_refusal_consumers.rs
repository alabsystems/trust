// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! EVERY `CleanIrRefusal` VARIANT IS RENDERED BY THE SHIPPED CONSUMER THAT NO
//! REPO GATE COMPILES.
//!
//! `CleanIrRefusal` is deliberately a CLOSED enum (no `#[non_exhaustive]`), so
//! that adding a variant is a compile error in every consumer that renders it:
//! its own doc states the rule it exists to keep — *"'Unsupported' with no next
//! step is a defect (v7/D3)"* — and a wildcard arm would let the next variant
//! reach an author as a category that names no next step. The closed enum is
//! the mechanism; this test is its VISIBILITY.
//!
//! The gap it closes, measured. `targo-trust/src/lean_build.rs` renders this
//! enum for the standalone `.lean` lane in `LeanBodyRefusal::ir_summary`, a
//! match with no wildcard arm. That file is in NEITHER Cargo workspace —
//! `targo-trust/Cargo.toml` declares its own `[workspace]`, and it is a member
//! of neither `crates/Cargo.toml` nor the root manifest — so
//! `targo --unverified test -p trust-clean-ir` and `-p trust-clean-ir-gate`
//! never compile it. `src/bootstrap/src/core/build_steps/check.rs` declares no
//! `tool_check_step!` for it either, so `x.py check --stage 1` does not reach
//! it. It IS built and installed by `build_steps/tool.rs`
//! (`ToolBuild { tool: "targo-trust" }` + `install_bin`) and
//! `scripts/run_tests_after_build.sh` requires `${STAGE2_BIN}/targo-trust`, so
//! the compile error surfaces at `x.py build --stage 2` — the release lane,
//! which is the most expensive possible place to find it. That happened: the
//! `ShapeMayNotCarryNat` variant landed with the arm missing, and every gate
//! the change ran was green.
//!
//! WHAT THIS TEST IS NOT. It does not compile `targo-trust`; it reads its
//! source. It therefore catches the recurrence of exactly this class — a new
//! variant with no arm, or a wildcard arm swallowing the next one — and
//! nothing else about that crate. The structural fix (a bootstrap check step,
//! or one workspace) is not this file.

use std::collections::BTreeSet;

/// The producer crate's own source — the authority on the variant list.
const REFUSAL_ENUM: &str = include_str!("../src/lib.rs");

/// The out-of-workspace consumer. Relative from `crates/trust-clean-ir/tests/`,
/// the same reach the compiler-source gates in `trust-clean-ir-gate` use.
const LEAN_BUILD: &str = include_str!("../../../targo-trust/src/lean_build.rs");

/// Drop `//` line comments so prose that names a variant cannot stand in for an
/// arm that renders it. Deliberately naive about `//` inside a string literal;
/// neither file has one, and a false NEGATIVE here (a dropped arm) fails the
/// test rather than hiding a gap.
fn strip_line_comments(source: &str) -> String {
    source
        .lines()
        .map(|line| line.find("//").map_or(line, |at| &line[..at]))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The source text between two markers, marker-exclusive at the end.
fn between<'a>(source: &'a str, start: &str, end: &str) -> &'a str {
    let from = source.find(start).unwrap_or_else(|| panic!("marker not found: {start}"));
    let rest = &source[from..];
    let to = rest.find(end).unwrap_or_else(|| panic!("marker not found after {start}: {end}"));
    &rest[..to]
}

/// Variant names of `pub enum CleanIrRefusal`, read off the declaration.
///
/// A variant is the only thing declared at four-space indent inside the enum
/// body that starts with an uppercase letter: fields sit at eight, doc comments
/// start with `///`, and the block ends at the first column-zero `}`.
fn declared_variants() -> BTreeSet<String> {
    let body =
        between(strip_line_comments(REFUSAL_ENUM).as_str(), "pub enum CleanIrRefusal {", "\n}")
            .to_owned();
    let variants: BTreeSet<String> = body
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("    ")?;
            if rest.starts_with(' ') {
                return None;
            }
            let name: String =
                rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
            let mut chars = name.chars();
            match chars.next() {
                Some(first) if first.is_ascii_uppercase() => Some(name),
                _ => None,
            }
        })
        .collect();
    assert!(
        variants.len() > 15,
        "the variant reader found {} variants, which means the parse broke, not that the enum \
         shrank to nothing: {variants:?}",
        variants.len(),
    );
    variants
}

#[test]
fn targo_trust_renders_every_clean_ir_refusal_variant() {
    let consumer = strip_line_comments(LEAN_BUILD);
    let summary = between(&consumer, "fn ir_summary(", "\n    fn detail(");
    let missing: Vec<String> = declared_variants()
        .into_iter()
        .filter(|variant| !summary.contains(&format!("CleanIrRefusal::{variant}")))
        .collect();
    assert!(
        missing.is_empty(),
        "`targo-trust/src/lean_build.rs::ir_summary` renders no arm for {missing:?}. That file \
         is in neither workspace and has no bootstrap check step, so the missing arm is an \
         `E0004` that first appears at `x.py build --stage 2`. Add the arm with the category \
         and next step this refusal asks an author for -- see this test's module doc.",
    );
}

#[test]
fn the_consumer_has_no_wildcard_arm_to_swallow_the_next_variant() {
    let consumer = strip_line_comments(LEAN_BUILD);
    let summary = between(&consumer, "fn ir_summary(", "\n    fn detail(");
    for wildcard in ["_ =>", "_ if", "other =>"] {
        assert!(
            !summary.contains(wildcard),
            "`ir_summary` grew a `{wildcard}` arm. That is what makes the closed enum stop \
             protecting this consumer: the next variant would reach a `.lean` author under \
             whatever category the wildcard picked, which is the defect `CleanIrRefusal`'s own \
             doc names (v7/D3). Render each variant, or state here why a wildcard is right.",
        );
    }
    // And the enum stays CLOSED. `#[non_exhaustive]` is the other way to make
    // this compile error go away, and it is the wrong one: it would oblige
    // every consumer to carry the wildcard the test above forbids.
    let declaration = REFUSAL_ENUM
        .find("pub enum CleanIrRefusal {")
        .expect("the enum declaration must be findable");
    let attributes = &REFUSAL_ENUM[declaration.saturating_sub(200)..declaration];
    assert!(
        !attributes.contains("non_exhaustive"),
        "`CleanIrRefusal` became `#[non_exhaustive]`. Then a consumer MUST carry a wildcard, and \
         a new variant reaches an author with no next step instead of failing to compile -- the \
         opposite of what the closed enum buys. The visibility problem it looks like a fix for is \
         what this file addresses instead.",
    );
}
