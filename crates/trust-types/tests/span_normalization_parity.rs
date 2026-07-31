// span_normalization_parity — pins the MEASURED divergence between Trust's rustc-`Span`
// converters so it cannot widen, narrow, or gain a copy without a deliberate edit.
//
// WHY THIS LIVES HERE: `trust_types::SourceSpan` is one of the two span types involved, and
// `trust-types` is a cheap, dependency-light workspace member. The converters themselves sit
// in crates that need `rustc_private` (`trust-mir-extract`, `trust-thir-lower` — both
// `exclude`d from `crates/Cargo.toml`'s workspace), inside `compiler/`, or inside the
// `first-party/trust-ir` submodule. None of them can be linked from an ordinary `cargo test`,
// and none can be exercised without a `TyCtxt`. So this is a SOURCE-level pin: it reads each
// converter's body and asserts its normalization fingerprint. (The behavioural half of the
// fix — the toolchain-build-token elision — is a plain string function and IS behaviourally
// tested, in `trust-types/src/model.rs::tests::stable_obligation_file_*`.)
//
// WHAT IT DEFENDS. Two conversion POLICIES stamp source positions in this tree:
//
//   * DEBUG-INFO conversion — `trust-thir-lower::to_source_span` and
//     `trust-ir/frontend/src/span_map.rs::to_ir`. The input span is REBASED to
//     `source_callsite()` (the user's invocation), the LO edge only is kept (a point), a
//     dummy span yields `None` (emit span-less), and the file renders as the SourceMap's own
//     name (`prefer_local_unconditionally()`), because the value is converted BACK to a
//     rustc `Span` (`to_mir.rs::span_from_source_span` matches it against `sm.files()`
//     names) and drives built-MIR `SourceInfo` and DWARF — a debugger stepping through
//     `assert!(..)` must stop at the user's line.
//
//   * OBLIGATION-IDENTITY conversion — `trust_verify.rs::source_span_from_rustc_span` and
//     its byte-identical copies (`trust-mir-extract::convert_span`,
//     `trust_r1_oracle.rs::source_span`). The RAW (not callsite-rebased) LO+HI range, a
//     dummy span yields `SourceSpan::default()`, and the file rendering is passed through
//     `trust_types::stable_obligation_file`, which elides the per-build `/rustc/<sha>/`
//     toolchain token so a sealed identity does not move when the compiler is rebuilt.
//     Compared exactly by R1's call-site multiset check, the box-deref lint drop set, and
//     `trust-router::strengthen_whole_program::SealedVcIdentity`. Rebasing to the callsite
//     is a MERGE, not a projection — it would collapse distinct calls inside one macro
//     invocation and weaken checks whose whole purpose is exactness.
//
// THE POLICY IS A PROPERTY OF THE PRODUCER, NOT OF THE TYPE. `trust_ir::value::SourceSpan`
// carries the debug-info quantity when `to_source_span`/`to_ir` stamp it on
// `InstrNode.span`, but the SAME type also carries raw identity-lane coordinates:
// `trust-ir-bridge/src/native_request.rs::obligation_sources_for_module` projects
// `ProofObligationSourceRange` — filled from `trust_types::SourceSpan` by
// `lower.rs::ObligationSourceMetadata::to_proof_source_identity` — into a
// `trust_ir::SourceSpan` on `NativeObligationSource.span`, which
// `crates/trust-wp/src/verifier_api.rs` equality-compares and `trust_verify.rs::
// native_source_span_json` serializes. Judge any span value by the converter that produced
// it; assuming the policy from the type name is exactly the mistake this pin exists to stop.
//
// The long-form analysis (why each policy is required for its own job, why the identity
// lane's raw location is still not user-actionable for macro-generated obligations, and why
// the remaining fix — a callsite anchor — must be ADDITIVE rather than a swap) lives as
// doc-comments at the converters:
//   - crates/trust-thir-lower/src/lib.rs :: LowerCx::to_source_span
//   - compiler/rustc_mir_transform/src/trust_verify.rs :: source_span_from_rustc_span
//
// If this test fails, READ THOSE FIRST. Do not "fix" it by editing the expectations to match
// new code — the expectations are the claim, the code is the evidence.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

/// Which `Loc` field the converter reads for the column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ColField {
    /// `Loc::col` — a 0-based `CharPos`. The trust-ir format's written contract
    /// (`first-party/trust-ir/crates/trust-ir/src/display.rs`, the `; #loc:` comment: the
    /// column is "0-BASED — the producer stores `CharPos.0` verbatim") and what
    /// `to_mir.rs::span_from_source_span` walks `char_indices()` with.
    CharPos,
    /// `Loc::col_display` — a terminal RENDERING width (`rustc_span/src/lib.rs`
    /// `lookup_file_pos_with_col_display` sums `char_width`). rustc's own comment there says
    /// it "is only used to properly show underlines in the terminal" and warns that tools
    /// consuming it naively are incorrect. Differs from `CharPos` on any line containing a
    /// tab or a wide char.
    ColDisplay,
}

/// How the converter renders the file name it stores.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FileRendering {
    /// `prefer_local_unconditionally()` verbatim — the SourceMap's own name for the file,
    /// including the remapped `/rustc/<sha>/…` virtual name for decoded sysroot files.
    /// REQUIRED for the debug-info lane: `to_mir.rs::span_from_source_span` resolves the
    /// file by matching this exact rendering against `sm.files()`, and DWARF wants the
    /// real (remapped) path.
    PreferLocalUnconditionally,
    /// The same rendering wrapped in `trust_types::stable_obligation_file`, which elides
    /// the per-build toolchain token (`/rustc/<sha>/` -> `/rustc/<toolchain>/`). REQUIRED
    /// for the identity lane: without it, `SealedVcIdentity.file` embedded the COMPILER's
    /// commit and every macro-generated obligation's sealed identity moved on each
    /// compiler rebuild. Behaviourally tested in `trust-types/src/model.rs`.
    RebuildStable,
    /// No file rendering detected — a line/col-only projection stores no file at all.
    NoneDetected,
}

/// What a converter does to a rustc `Span` on its way to a stored source position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Fingerprint {
    /// REBASES its own input span to `Span::source_callsite()` before reading coordinates
    /// (a self-rebinding, `sp = sp.source_callsite()`), i.e. the STORED range is the
    /// user's invocation, not the macro-definition position. The one irreconcilable axis
    /// between the two lanes: the rebase is a merge, so no later projection recovers the
    /// macro-definition position from it, and none recovers the invocation from a raw
    /// span. NOTE this axis deliberately does NOT fire on an ADDITIVE callsite anchor —
    /// a converter may bind `span.source_callsite()` to a NEW name and carry it BESIDE
    /// the raw range (that is the prescribed evolution for making macro-generated
    /// obligation locations actionable). What it pins out of the identity lane is the
    /// anti-conservative SWAP, where the raw coordinates themselves get rebased.
    rebases_to_callsite: bool,
    /// Reads `span.hi()` as well as `span.lo()` — i.e. stores a RANGE, not a point.
    records_hi: bool,
    /// Which `Loc` column field is read.
    col_field: ColField,
    /// Adds 1 to the column, i.e. re-bases it to 1.
    col_plus_one: bool,
    /// A dummy span yields "no location" as `None` (rather than a zero-valued default).
    dummy_yields_none: bool,
    /// How the stored file name is rendered.
    file_rendering: FileRendering,
}

/// One pinned converter.
struct Site {
    /// Repo-relative path.
    path: &'static str,
    /// Function name; matched as `fn <name>` followed by `(` or `<`.
    func: &'static str,
    /// The type it produces, for the failure message.
    produces: &'static str,
    /// Present-tree behaviour.
    expect: Fingerprint,
    /// The fingerprint a KNOWN-DEFECT repair of this converter will produce, where one is
    /// prescribed. Matching it is GREEN: the repair is what this pin wants, and it must not
    /// go red at the moment the repair lands (for a submodule site, that moment is a
    /// gitlink bump whose CI never saw the change). `None` for a site whose `expect` IS the
    /// correct behaviour.
    repaired: Option<Fingerprint>,
    /// Why this fingerprint is what it is — quoted verbatim into any failure.
    rationale: &'static str,
}

/// THE PINNED MATRIX. Six converters, two lanes, one deliberate divergence
/// (`rebases_to_callsite`, plus the lanes' opposite file renderings) and one still-open
/// defect (`span_map.rs`'s column, with its repair fingerprint pre-accepted).
fn sites() -> Vec<Site> {
    vec![
        // ---- DEBUG-INFO lane ------------------------------------------------------------
        Site {
            path: "crates/trust-thir-lower/src/lib.rs",
            func: "to_source_span",
            produces: "trust_ir::value::SourceSpan",
            expect: Fingerprint {
                rebases_to_callsite: true,
                records_hi: false,
                col_field: ColField::CharPos,
                col_plus_one: false,
                dummy_yields_none: true,
                file_rendering: FileRendering::PreferLocalUnconditionally,
            },
            repaired: None,
            rationale: "CORRECT for its job. Debug-info stamp: callsite-rebased so a \
                        debugger stops at the user's line; LO-only because a DWARF row is a \
                        point; 0-based CharPos verbatim, matching the trust-ir format's \
                        written `; #loc:` contract and the `to_mir.rs::span_from_source_span` \
                        round trip; the SourceMap's own file rendering, because the round \
                        trip matches it against `sm.files()` names.",
        },
        Site {
            path: "first-party/trust-ir/frontend/src/span_map.rs",
            func: "to_ir",
            produces: "trust_ir::value::SourceSpan",
            expect: Fingerprint {
                rebases_to_callsite: true,
                records_hi: false,
                col_field: ColField::ColDisplay,
                col_plus_one: true,
                dummy_yields_none: true,
                file_rendering: FileRendering::PreferLocalUnconditionally,
            },
            // The prescribed repair: store `CharPos.0` verbatim, per the format's own
            // written contract. Landing it in the submodule turns `expect` stale and
            // matches THIS fingerprint instead — deliberately green, so the repair does
            // not red Trust's suite at gitlink-bump time. Once it lands, fold it into
            // `expect` and drop this.
            repaired: Some(Fingerprint {
                rebases_to_callsite: true,
                records_hi: false,
                col_field: ColField::CharPos,
                col_plus_one: false,
                dummy_yields_none: true,
                file_rendering: FileRendering::PreferLocalUnconditionally,
            }),
            rationale: "DEFECTIVE COLUMN, KNOWN AND PINNED AS SUCH (this file is in the \
                        `first-party/trust-ir` submodule, and CLAUDE.md requires cross-repo \
                        changes to go through a separate checkout + a deliberate gitlink \
                        bump — so the repair fingerprint is pre-accepted above rather than \
                        patched here). It writes the SAME type as `to_source_span` but emits \
                        `col_display + 1`, breaking the format contract twice: `col_display` \
                        is a terminal rendering width, and `+ 1` re-bases to 1. Fed to \
                        `to_mir.rs::span_from_source_span` this lands one char right on an \
                        ASCII line, arbitrarily far off on a line with a tab or wide char, \
                        and for the common `shrink_to_hi()` end-of-line stamp overruns to \
                        `chars_in_line + 1`, which fails closed to `None` and drops the span.",
        },
        // ---- OBLIGATION-IDENTITY lane ---------------------------------------------------
        // These three MUST stay identical to each other (modulo comments, whitespace, and
        // `trust_types::` qualification): R1's `exact_callsite_span_multiset_matches`
        // compares the oracle's spans (`trust_r1_oracle::source_span`) against producer VC
        // locations (`trust-mir-extract::convert_span`), and the box-deref lint drop set
        // matches `source_span_from_rustc_span` output against `convert_span`-stamped
        // spans — so normalizing one copy alone makes those exact comparisons fail closed
        // on every span that differs.
        Site {
            path: "compiler/rustc_mir_transform/src/trust_verify.rs",
            func: "source_span_from_rustc_span",
            produces: "trust_types::SourceSpan",
            expect: Fingerprint {
                rebases_to_callsite: false,
                records_hi: true,
                col_field: ColField::CharPos,
                col_plus_one: false,
                dummy_yields_none: false,
                file_rendering: FileRendering::RebuildStable,
            },
            repaired: None,
            rationale: "RAW ON PURPOSE. This value is an obligation identity key before it \
                        is a diagnostic; rebasing it to the callsite would merge distinct \
                        calls inside one macro invocation. Its raw location is still not \
                        user-actionable for macro-generated obligations (see the doc-comment \
                        at this site) — that fix is an ADDITIVE callsite anchor, which this \
                        axis deliberately permits, never a swap. The file rendering elides \
                        the toolchain build token so the sealed identity survives compiler \
                        rebuilds.",
        },
        Site {
            path: "crates/trust-mir-extract/src/convert.rs",
            func: "convert_span",
            produces: "trust_types::SourceSpan",
            expect: Fingerprint {
                rebases_to_callsite: false,
                records_hi: true,
                col_field: ColField::CharPos,
                col_plus_one: false,
                dummy_yields_none: false,
                file_rendering: FileRendering::RebuildStable,
            },
            repaired: None,
            rationale: "Identical sibling of `trust_verify::source_span_from_rustc_span`.",
        },
        Site {
            path: "compiler/rustc_mir_transform/src/trust_r1_oracle.rs",
            func: "source_span",
            produces: "trust_types::SourceSpan",
            expect: Fingerprint {
                rebases_to_callsite: false,
                records_hi: true,
                col_field: ColField::CharPos,
                col_plus_one: false,
                dummy_yields_none: false,
                file_rendering: FileRendering::RebuildStable,
            },
            repaired: None,
            rationale: "Identical sibling of `trust_verify::source_span_from_rustc_span`.",
        },
        Site {
            path: "compiler/rustc_mir_transform/src/trust_r1_oracle.rs",
            func: "span_line_col",
            produces: "(u32, u32)",
            expect: Fingerprint {
                rebases_to_callsite: false,
                records_hi: false,
                col_field: ColField::CharPos,
                col_plus_one: false,
                dummy_yields_none: false,
                file_rendering: FileRendering::NoneDetected,
            },
            repaired: None,
            rationale: "The identity lane's OWN LO-only projection; stores no file. \
                        Load-bearing evidence that LO-vs-LO+HI is NOT what blocks \
                        cross-lane comparison — the identity lane already drops HI \
                        wherever it needs a key (here, and in `SealedVcIdentity`). The \
                        callsite rebase is the only irreconcilable axis.",
        },
    ]
}

/// Coordinate-reading rustc `SourceMap`/`SourceFile` APIs a new converter would go through.
const CONVERTER_APIS: &[&str] =
    &["lookup_char_pos(", "lookup_file_pos_with_col_display(", "span_to_lines(", "lookup_line("];

/// Every file under the SCANNED ROOTS that calls one of [`CONVERTER_APIS`]. A new entry
/// means a new converter that this test has not judged.
const CONVERTER_FILES: &[&str] = &[
    "compiler/rustc_mir_transform/src/trust_r1_oracle.rs",
    "compiler/rustc_mir_transform/src/trust_verify.rs",
    "crates/trust-mir-extract/src/convert.rs",
    "crates/trust-thir-lower/src/lib.rs",
    "first-party/trust-ir/frontend/src/span_map.rs",
];

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is <repo>/crates/trust-types.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").canonicalize().expect("repo root")
}

/// Drop `//` line comments so a doc/inline comment that merely NAMES `source_callsite` cannot
/// register as a call — and so a comment-only edit to one identity-lane copy cannot fail the
/// cross-copy identity test. (None of the pinned bodies contain a `//` inside a string
/// literal.)
fn strip_line_comments(src: &str) -> String {
    src.lines()
        .map(|line| match line.find("//") {
            Some(i) => &line[..i],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Extract the body of `fn <name>` by brace-matching from the first `{` after the signature.
/// Returns `None` if the function is absent (which the caller reports as a failure).
fn fn_body(src: &str, name: &str) -> Option<String> {
    let needle = format!("fn {name}");
    let mut from = 0usize;
    let start = loop {
        let at = from + src[from..].find(&needle)?;
        // Require a real token boundary: `fn name(` or `fn name<`, not `fn name_longer`.
        let after = src[at + needle.len()..].chars().next();
        if matches!(after, Some('(') | Some('<')) {
            break at;
        }
        from = at + needle.len();
    };
    // No pinned signature contains a `{` before its body brace.
    let open = start + src[start..].find('{')?;
    let bytes = src.as_bytes();
    let mut depth = 0usize;
    for (offset, &b) in bytes[open..].iter().enumerate() {
        match b {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(src[open + 1..open + offset].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

/// True iff the (comment-stripped) body REBASES its own input span to the callsite: a
/// self-rebinding `<name> = <name>.source_callsite()`, with or without `let`. An ADDITIVE
/// anchor binds a NEW name (`let anchor = span.source_callsite();`) and does not match —
/// see the `rebases_to_callsite` axis doc for why that distinction is the whole point.
fn rebases_input_to_callsite(stripped: &str) -> bool {
    const NEEDLE: &str = ".source_callsite()";
    let is_ident = |c: char| c.is_alphanumeric() || c == '_';
    let mut from = 0usize;
    while let Some(found) = stripped[from..].find(NEEDLE) {
        let at = from + found;
        from = at + NEEDLE.len();
        let before = &stripped[..at];
        // The receiver identifier immediately left of `.source_callsite()`.
        let recv_start = before.rfind(|c: char| !is_ident(c)).map(|i| i + 1).unwrap_or(0);
        let recv = &before[recv_start..];
        if recv.is_empty() {
            continue;
        }
        // Walk left: `=` (a single one — `==`/`!=`/`>=` etc. do not qualify), then the
        // SAME identifier, at a token boundary. Covers `sp = sp.source_callsite()` and
        // `let sp = sp.source_callsite();`.
        let pre = before[..recv_start].trim_end();
        let Some(pre) = pre.strip_suffix('=') else { continue };
        if pre.ends_with(['=', '!', '<', '>', '+', '-', '*', '/']) {
            continue;
        }
        let pre = pre.trim_end();
        if pre.ends_with(recv) && !pre[..pre.len() - recv.len()].ends_with(is_ident) {
            return true;
        }
    }
    false
}

fn fingerprint(body: &str) -> Fingerprint {
    let b = strip_line_comments(body);
    let col_field =
        if b.contains("col_display") { ColField::ColDisplay } else { ColField::CharPos };
    let file_rendering = if b.contains("stable_obligation_file(") {
        FileRendering::RebuildStable
    } else if b.contains("prefer_local_unconditionally()") {
        FileRendering::PreferLocalUnconditionally
    } else {
        FileRendering::NoneDetected
    };
    Fingerprint {
        rebases_to_callsite: rebases_input_to_callsite(&b),
        records_hi: b.contains(".hi()"),
        col_field,
        // Today only span_map's `unwrap_or(u32::MAX - 1) + 1` matches. Any other `+ 1` that
        // appears in one of these bodies is itself worth a human read, so firing is correct.
        col_plus_one: b.contains("+ 1"),
        dummy_yields_none: b.contains("return None"),
        file_rendering,
    }
}

/// Collect repo-relative paths of `.rs` files under `root` that call a [`CONVERTER_APIS`]
/// entry.
fn scan_for_converters(repo: &Path, rel_root: &str, out: &mut Vec<String>) {
    let root = repo.join(rel_root);
    if !root.exists() {
        return;
    }
    let mut stack = vec![root];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if path.is_dir() {
                // Build outputs and tool scratch are not source.
                if matches!(name.as_ref(), "target" | ".git" | ".claude" | "build" | "node_modules")
                {
                    continue;
                }
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let rel = path.strip_prefix(repo).unwrap_or(&path);
                let rel = rel.to_string_lossy().replace('\\', "/");
                // This file carries the probe strings itself; it is not a converter.
                if rel.ends_with("tests/span_normalization_parity.rs") {
                    continue;
                }
                let Ok(src) = std::fs::read_to_string(&path) else { continue };
                if CONVERTER_APIS.iter().any(|needle| src.contains(needle)) {
                    out.push(rel);
                }
            }
        }
    }
}

#[test]
fn span_converters_match_their_pinned_normalization() {
    let repo = repo_root();
    let mut failures: Vec<String> = Vec::new();
    let mut checked = 0usize;
    let mut skipped: Vec<&str> = Vec::new();

    for site in sites() {
        let path = repo.join(site.path);
        if !path.exists() {
            // The only legitimately-absent path is the `first-party/trust-ir` submodule,
            // which a superproject clone may not have materialized.
            if site.path.starts_with("first-party/") {
                skipped.push(site.path);
                continue;
            }
            failures.push(format!("{}: file is missing from the tree", site.path));
            continue;
        }
        let src = std::fs::read_to_string(&path).expect("read converter source");
        let Some(body) = fn_body(&src, site.func) else {
            failures.push(format!(
                "{}: `fn {}` not found. It was the {} converter; if it was renamed or \
                 deleted, update this test's matrix DELIBERATELY.",
                site.path, site.func, site.produces
            ));
            continue;
        };
        let got = fingerprint(&body);
        checked += 1;
        if got == site.expect {
            continue;
        }
        if let Some(repaired) = site.repaired {
            if got == repaired {
                // The prescribed repair landed: green by design. Fold `repaired` into
                // `expect` on the next deliberate edit of this matrix.
                continue;
            }
        }
        failures.push(format!(
            "\n  {}::{} (-> {})\n    expected: {:?}{}\n    actual:   {:?}\n    \
             pinned because: {}",
            site.path,
            site.func,
            site.produces,
            site.expect,
            match site.repaired {
                Some(repaired) => format!("\n    (also accepted, the repair: {repaired:?})"),
                None => String::new(),
            },
            got,
            site.rationale
        ));
    }

    assert!(
        failures.is_empty(),
        "Span normalization drifted from the pinned matrix.\n{}\n\n\
         Read the doc-comments at crates/trust-thir-lower/src/lib.rs::to_source_span and \
         compiler/rustc_mir_transform/src/trust_verify.rs::source_span_from_rustc_span before \
         changing anything here. In particular: rebasing a stored range to `source_callsite()` \
         is a MERGE, not a projection. Doing it to the trust_types lane collapses distinct \
         calls inside one macro invocation, weakening R1's exact call-site multiset check and \
         widening the missing-SAFETY lint drop set over user-written code. (Carrying an \
         ADDITIVE callsite anchor beside the raw range, bound to a new name, is fine — that \
         is the prescribed fix for macro-generated obligation locations.)",
        failures.join("\n")
    );

    // Guard against the matrix quietly emptying out.
    let expected_min = if skipped.is_empty() { 6 } else { 5 };
    assert!(
        checked >= expected_min,
        "only {checked} converters were checked (expected >= {expected_min}); skipped: {skipped:?}"
    );
}

#[test]
fn the_two_identity_lane_copies_are_byte_identical() {
    // R1's `exact_callsite_span_multiset_matches` compares spans produced by the oracle
    // against spans stamped on VCs by the producer. If these bodies drift apart, R1 stops
    // matching on exactly the spans that differ — silently, and fail-closed, so the symptom
    // is lost coverage rather than a crash.
    let repo = repo_root();
    let copies = [
        ("compiler/rustc_mir_transform/src/trust_verify.rs", "source_span_from_rustc_span"),
        ("crates/trust-mir-extract/src/convert.rs", "convert_span"),
        ("compiler/rustc_mir_transform/src/trust_r1_oracle.rs", "source_span"),
    ];

    let mut bodies: Vec<(String, String)> = Vec::new();
    for (path, func) in copies {
        let src = std::fs::read_to_string(repo.join(path)).expect("read converter source");
        let body = fn_body(&src, func).unwrap_or_else(|| panic!("{path}: `fn {func}` not found"));
        // Normalize the legitimate differences: comments (each copy documents itself —
        // a comment edit in one file must not fail this test), whitespace, and the
        // crate-qualification of trust-types items (`SourceSpan` vs
        // `trust_types::SourceSpan`).
        let normalized = strip_line_comments(&body)
            .replace("trust_types::", "")
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        bodies.push((format!("{path}::{func}"), normalized));
    }

    let (ref reference_name, ref reference) = bodies[0];
    for (name, body) in &bodies[1..] {
        assert_eq!(
            reference, body,
            "\n{reference_name} and {name} must stay identical modulo comments, whitespace, \
             and the `trust_types::` prefix, because R1's \
             `exact_callsite_span_multiset_matches` compares the spans they produce against \
             each other. Change all three together or none.\n"
        );
    }
}

#[test]
fn no_unjudged_span_converter_appeared() {
    // WHAT THIS ENFORCES, exactly: no file under the scanned roots (crates/,
    // compiler/rustc_mir_transform/, first-party/trust-ir/, targo-trust/) starts reading
    // rustc span coordinates through one of `CONVERTER_APIS` without appearing here. It is
    // a tripwire over the surfaces Trust owns, not a proof of global exhaustiveness. What
    // it cannot see, deliberately not overclaimed:
    //   * a span built by PROJECTING an already-converted value — e.g.
    //     `trust-ir-bridge/src/native_request.rs::obligation_sources_for_module`, which
    //     projects a `ProofObligationSourceRange` (raw identity-lane data) into a
    //     `trust_ir::SourceSpan`. A projection inherits its lane from its source; such
    //     sites are judged in the converters' doc-comments, not fingerprinted here.
    //   * upstream `compiler/` crates outside rustc_mir_transform (rustc itself calls
    //     these APIs constantly, for its own diagnostics) and first-party siblings other
    //     than trust-ir. A Trust-authored converter there would be a design breach the
    //     `// Trust:` review discipline has to catch, not this test.
    let repo = repo_root();
    let mut found: Vec<String> = Vec::new();
    scan_for_converters(&repo, "crates", &mut found);
    scan_for_converters(&repo, "compiler/rustc_mir_transform", &mut found);
    scan_for_converters(&repo, "first-party/trust-ir", &mut found);
    scan_for_converters(&repo, "targo-trust", &mut found);
    found.sort();
    found.dedup();

    // The submodule may be unmaterialized in a bare superproject clone.
    let mut expected: Vec<String> = CONVERTER_FILES
        .iter()
        .filter(|p| !p.starts_with("first-party/") || repo.join(p).exists())
        .map(|p| (*p).to_string())
        .collect();
    expected.sort();

    assert_eq!(
        expected, found,
        "\nThe set of scanned Trust-owned files calling a span-coordinate API changed.\n\
         A new file here is a NEW span converter that has not been judged against the two \
         lanes. Add it to `sites()` with an explicit fingerprint and rationale, or route it \
         through an existing converter. A file disappearing means a converter was deleted or \
         renamed — confirm the lane it served still has one.\n"
    );
}
