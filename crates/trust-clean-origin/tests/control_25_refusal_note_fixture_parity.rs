// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 25 — the refusal a USER sees is the refusal this crate renders.**
//!
//! # The gap this control closes
//!
//! Two committed `ui` fixtures carry the `BitVec` story's whole user-visible
//! surface in their `.stderr`: `clean_origin_bitvec_widths.stderr` (a literal
//! width CARRIES and is then refused by the reflection) and
//! `clean_origin_bitvec_nonliteral_width.stderr` (a non-literal width is
//! refused by the CARRIER, by name). Both texts are produced by
//! `EmitRefusal::note()` / `MintRefusal::note()` in this crate —
//! `rustc_resolve::trust_clean_mint` copies the string into
//! `CleanOriginRefusal { note }` verbatim.
//!
//! Nothing checked that the two agreed. `CLAUDE.md`'s own corollary is that
//! **no pre-push lane runs a `ui` test** — the `push` profile compiles the
//! compiler and its test targets but executes no `compiletest` — so an edit to
//! either `note()` lands green with the fixture stale, and an edit to a
//! fixture lands green with the renderer stale. The refusal is the ONLY thing
//! a user of this lane ever gets (ruling v7/D3: a refusal must carry the fix,
//! with options), so a drift between them is a drift in the product.
//!
//! This control runs in the fast `crates/` lane, needs no compiler build, and
//! fails if either side moves without the other.
//!
//! # What it does NOT prove
//!
//! It does not run `compiletest`, so it says nothing about the `ERROR`/`NOTE`
//! annotations, the spans, or the error code. It pins the note BODY, which is
//! the part that carries the explanation and the options.

use clean_kernel::{Environment, Expr, Name};
use trust_clean_carrier::carrier_signature_for;
use trust_clean_origin::{decide_mint, plan_clean_origin_body};
use trust_symbols::{AxiomClosure, CicKernelRecheck, KernelAuthority, KernelStatus, TermDigest};

/// The two fixtures' island sources, copied from the `ui` files themselves so
/// the declarations under test are the declarations the user compiled.
const WIDTHS_ISLAND: &str = r"
def bv8  (x : BitVec 8)  : BitVec 8  := x
def bv16 (x : BitVec 16) : BitVec 16 := x
def bv32 (x : BitVec 32) : BitVec 32 := x
def bv64 (x : BitVec 64) : BitVec 64 := x
def bvmix (a : BitVec 64) (b : BitVec 8) : BitVec 8 := b
";

const NONLITERAL_ISLAND: &str = r"
def w : Nat := 64
def bvdef  (x : BitVec w)         : BitVec w         := x
def bvexpr (x : BitVec (32 + 32)) : BitVec (32 + 32) := x
";

fn island(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn type_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("the island registered no constant `{name}`"))
        .type_
        .clone()
}

fn kernel_checked() -> KernelStatus {
    CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"a term the kernel re-checked"),
        AxiomClosure::audited([]),
    )
}

fn fixture(file: &str) -> String {
    let path = format!("{}/../../tests/ui/trust/{file}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read `{path}`: {e}"))
}

/// Pull `name -> note body` out of a committed `.stderr`.
///
/// `rustc` prints a `CleanOriginRefusal`'s note as `   = note: <first line>`
/// followed by continuation lines indented by exactly 11 spaces, and it does
/// NOT re-wrap: the fixtures carry lines hundreds of columns wide. The
/// renderers emit no line with leading whitespace (every `\n\` continuation in
/// the format string strips the source indentation), so stripping the fixed
/// prefix is exact and needs no heuristic.
fn notes_from_stderr(stderr: &str) -> Vec<(String, String)> {
    const HEAD: &str = "   = note: ";
    const CONT: &str = "           ";
    let mut out: Vec<(String, String)> = Vec::new();
    let mut current: Option<String> = None;
    let mut lines = stderr.lines().peekable();
    while let Some(line) = lines.next() {
        if let Some(rest) = line.strip_prefix("error[E0425]: cannot find function `") {
            current = rest.split('`').next().map(str::to_owned);
            continue;
        }
        let Some(first) = line.strip_prefix(HEAD) else { continue };
        let Some(name) = current.clone() else { continue };
        if out.iter().any(|(n, _)| *n == name) {
            continue; // only the first `= note:` of an error is the refusal
        }
        let mut body = vec![first.to_owned()];
        while let Some(next) = lines.peek() {
            let Some(rest) = next.strip_prefix(CONT) else { break };
            body.push(rest.to_owned());
            lines.next();
        }
        out.push((name, body.join("\n")));
    }
    out
}

fn assert_parity(file: &str, rendered: &[(&str, String)]) {
    let stderr = fixture(file);
    let committed = notes_from_stderr(&stderr);
    assert_eq!(
        committed.len(),
        rendered.len(),
        "`{file}` carries {} E0425 notes but this crate renders {} — the fixture and the \
         renderer have diverged in SHAPE, not just in text",
        committed.len(),
        rendered.len()
    );
    for ((got_name, got_note), (want_name, want_note)) in committed.iter().zip(rendered) {
        assert_eq!(
            got_name, want_name,
            "`{file}` reports its refusals in a different order than this test renders them"
        );
        assert_eq!(
            got_note.trim_end(),
            want_note.trim_end(),
            "\n\nThe note committed in `tests/ui/trust/{file}` for `{got_name}` is NOT what \
             this crate renders today.\n\
             A user reads the fixture's version; ruling v7/D3 says that text IS the fix, so \
             the two may not drift.\n\
             Fix whichever is stale — if you just edited a `note()` renderer, update the \
             `.stderr` (no pre-push lane runs the `ui` suite, so nothing else will tell \
             you).\n\n\
             --- committed in the fixture ---\n{got_note}\n\
             --- rendered by this crate ---\n{want_note}\n"
        );
    }
}

/// The literal-width family: carried, then refused by the REFLECTION.
#[test]
fn widths_fixture_matches_the_emit_refusal_renderer() {
    let env = island(WIDTHS_ISLAND);
    let rendered: Vec<(&str, String)> = ["bv8", "bv16", "bv32", "bv64", "bvmix"]
        .into_iter()
        .map(|name| {
            let refusal = plan_clean_origin_body(&env, name)
                .expect_err("a BitVec-typed signature must not plan");
            (name, refusal.note())
        })
        .collect();
    assert_parity("clean_origin_bitvec_widths.stderr", &rendered);
}

/// The non-literal-width twin: refused by the CARRIER, through the mint.
///
/// This reproduces `trust_clean_mint::decide`'s own call exactly — the carrier
/// it hands `decide_mint` is `carrier_signature_for(..).map(|s| s.result().clone())`,
/// so the `CarrierRefused` inside the note is the SIGNATURE-level one.
#[test]
fn nonliteral_fixture_matches_the_mint_refusal_renderer() {
    let env = island(NONLITERAL_ISLAND);
    let status = kernel_checked();
    let rendered: Vec<(&str, String)> = ["bvdef", "bvexpr"]
        .into_iter()
        .map(|name| {
            let carrier = carrier_signature_for(&type_of(&env, name)).map(|s| s.result().clone());
            let refusal = decide_mint(name, &status, carrier)
                .expect_err("a non-literal width has no carrier, so no DefId");
            (name, refusal.note())
        })
        .collect();
    assert_parity("clean_origin_bitvec_nonliteral_width.stderr", &rendered);
}

/// MUTATION CONTROL — the parity assertion is not vacuous.
///
/// Both halves above would pass trivially if `notes_from_stderr` returned
/// empty bodies, or if the comparison were a `contains`. This mutates one
/// character of a rendered note and requires the extractor to notice, and it
/// separately requires the extracted body to be substantial and to carry the
/// two things v7/D3 demands.
#[test]
fn the_parity_check_can_fail() {
    let stderr = fixture("clean_origin_bitvec_widths.stderr");
    let committed = notes_from_stderr(&stderr);
    assert_eq!(committed.len(), 5, "five E0425 refusals are committed in that fixture");
    for (name, body) in &committed {
        assert!(
            body.len() > 500,
            "`{name}`'s extracted note is {} bytes — the extractor is dropping continuation \
             lines, which would make the parity assertion pass on a stub",
            body.len()
        );
        assert!(body.contains("options:"), "v7/D3: `{name}`'s note must carry options");
        assert!(
            body.lines().count() > 3,
            "`{name}`'s note must be multi-line, or the 11-space continuation strip is dead"
        );
    }

    // A one-character mutation must be caught. `assert_parity` compares with
    // `assert_eq!`, so this stands in for it: the same comparison, inverted.
    let (_, first) = &committed[0];
    let mutated = first.replacen("carries TOTALLY", "carries totally", 1);
    assert_ne!(&mutated, first, "the mutation must actually change the text");
    assert_ne!(
        mutated.trim_end(),
        first.trim_end(),
        "a one-word change to a note must make the parity comparison fail"
    );
}

/// The blessing half — how a note edit is carried into the fixtures.
///
/// `compiletest --bless` would do this, but it needs a built stage1 compiler
/// (tens of minutes, and it takes the exclusive build-tree lock), which is
/// exactly why the two sides drifted in the first place. With
/// `TRUST_BLESS_UI_NOTES=1` this rewrites the `= note:` BODY of each `E0425`
/// block in the two fixtures from the renderers above, touching nothing else —
/// not a span, not an error code, not a `~^` annotation. It is a bless hook, not
/// a check: `#[ignore]`d, so the default `crates/` lane never runs it, never
/// writes to `tests/` and never counts it as a pass; and without the variable it
/// panics with the recipe, so a bare `--ignored` run cannot pass having blessed
/// nothing.
#[test]
#[ignore = "bless hook: set TRUST_BLESS_UI_NOTES=1 and run with --ignored to rewrite the \
            tests/ui/trust E0425 note bodies"]
fn bless_the_ui_notes_when_asked() {
    if std::env::var_os("TRUST_BLESS_UI_NOTES").is_none() {
        panic!(
            "bless_the_ui_notes_when_asked is a bless hook and TRUST_BLESS_UI_NOTES is unset, \
             so it blessed nothing. Run: TRUST_BLESS_UI_NOTES=1 targo --unverified test \
             --manifest-path crates/Cargo.toml -p trust-clean-origin \
             --test control_25_refusal_note_fixture_parity -- --ignored --exact \
             bless_the_ui_notes_when_asked"
        );
    }
    let widths_env = island(WIDTHS_ISLAND);
    let widths: Vec<(String, String)> = ["bv8", "bv16", "bv32", "bv64", "bvmix"]
        .into_iter()
        .map(|name| {
            (name.to_owned(), plan_clean_origin_body(&widths_env, name).unwrap_err().note())
        })
        .collect();

    let nonliteral_env = island(NONLITERAL_ISLAND);
    let status = kernel_checked();
    let nonliteral: Vec<(String, String)> = ["bvdef", "bvexpr"]
        .into_iter()
        .map(|name| {
            let carrier =
                carrier_signature_for(&type_of(&nonliteral_env, name)).map(|s| s.result().clone());
            (name.to_owned(), decide_mint(name, &status, carrier).unwrap_err().note())
        })
        .collect();

    for (file, notes) in [
        ("clean_origin_bitvec_widths.stderr", widths),
        ("clean_origin_bitvec_nonliteral_width.stderr", nonliteral),
    ] {
        let path = format!("{}/../../tests/ui/trust/{file}", env!("CARGO_MANIFEST_DIR"));
        let original = std::fs::read_to_string(&path).expect("the fixture exists");
        let mut out: Vec<String> = Vec::new();
        let mut current: Option<String> = None;
        let mut done: Vec<String> = Vec::new();
        let mut lines = original.lines().peekable();
        while let Some(line) = lines.next() {
            if let Some(rest) = line.strip_prefix("error[E0425]: cannot find function `") {
                current = rest.split('`').next().map(str::to_owned);
                out.push(line.to_owned());
                continue;
            }
            let Some(name) = current.clone() else {
                out.push(line.to_owned());
                continue;
            };
            if !line.starts_with("   = note: ") || done.contains(&name) {
                out.push(line.to_owned());
                continue;
            }
            // Drop the old body, emit the new one.
            while lines.peek().is_some_and(|n| n.starts_with("           ")) {
                lines.next();
            }
            let note = &notes
                .iter()
                .find(|(n, _)| *n == name)
                .unwrap_or_else(|| panic!("no rendered note for `{name}` in `{file}`"))
                .1;
            for (i, body) in note.lines().enumerate() {
                out.push(format!("{}{body}", if i == 0 { "   = note: " } else { "           " }));
            }
            done.push(name);
        }
        let mut text = out.join("\n");
        if original.ends_with('\n') {
            text.push('\n');
        }
        std::fs::write(&path, text).expect("the fixture is writable");
        eprintln!("blessed {file} ({} notes)", done.len());
    }
}

/// The other half of "no pre-push lane runs the `ui` suite": the SPANS.
///
/// A `.stderr` names source lines by number (`--> $DIR/f.rs:82:23`) and then
/// quotes them (`LL |     let _ = …`). Adding a line to a fixture's `//!`
/// header shifts every one of those numbers, and nothing in the fast lane
/// notices — the next reader to run `compiletest` inherits the failure and has
/// to work out which of the intervening commits caused it.
///
/// This checks the quoted line IS the line the number points at, in both
/// `BitVec` fixtures, straight off the committed files. It is not a substitute
/// for `compiletest` — it cannot see a missing diagnostic or a wrong column —
/// but it catches the one drift that a header edit causes every time.
#[test]
fn the_fixture_line_numbers_point_at_the_lines_they_quote() {
    for stem in ["clean_origin_bitvec_widths", "clean_origin_bitvec_nonliteral_width"] {
        let source: Vec<String> =
            fixture(&format!("{stem}.rs")).lines().map(str::to_owned).collect();
        let stderr = fixture(&format!("{stem}.stderr"));
        let lines: Vec<&str> = stderr.lines().collect();
        let marker = format!("$DIR/{stem}.rs:");
        let mut checked = 0_usize;
        for (i, line) in lines.iter().enumerate() {
            let Some(rest) = line.split(&marker).nth(1) else { continue };
            let mut parts = rest.split(':');
            let number: usize =
                parts.next().and_then(|n| n.parse().ok()).expect("a line number follows the path");
            // `-->` line, then the `   |` gutter, then the quoted source.
            let quoted = lines
                .get(i + 2)
                .and_then(|l| l.strip_prefix("LL |"))
                .unwrap_or_else(|| panic!("`{stem}.stderr` line {} quotes no source", i + 3));
            let quoted = quoted.strip_prefix(' ').unwrap_or(quoted);
            let actual = source
                .get(number - 1)
                .unwrap_or_else(|| panic!("`{stem}.rs` has no line {number}"));
            assert_eq!(
                quoted.trim_end(),
                actual.trim_end(),
                "`{stem}.stderr` says line {number} is `{quoted}`, but `{stem}.rs` line \
                 {number} is `{actual}`. The fixture's line numbers have drifted — almost \
                 always because a `//!` header grew. Shift every `$DIR/{stem}.rs:<n>` by the \
                 number of lines added."
            );
            checked += 1;
        }
        assert!(checked >= 2, "`{stem}.stderr` must carry span references; found {checked}");
    }
}
