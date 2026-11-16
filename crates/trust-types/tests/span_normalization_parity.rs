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
//     dummy span yields `None` (emit span-less), and the file renders as the REMAPPED name
//     (`prefer_remapped_unconditionally()`, the `--remap-path-prefix` projection — WS5.9/WS8.9,
//     F-117), because `Module.files` is module content that every module digest covers, so
//     the local checkout path must never reach it. The value is converted BACK to a rustc
//     `Span` (`to_mir.rs::ResolvedFiles` resolves it against `sm.files()` by the SAME
//     projection, refuses a non-injective remap, and falls back to the local rendering) and
//     drives built-MIR `SourceInfo` and DWARF — a debugger stepping through `assert!(..)`
//     must stop at the user's line.
//
//   * OBLIGATION-IDENTITY conversion — `trust_verify.rs::source_span_from_rustc_span` and
//     its byte-identical copies (`trust-mir-extract::convert_span`,
//     `trust_r1_oracle.rs::source_span`). The RAW (not callsite-rebased) LO+HI range, a
//     dummy span yields `SourceSpan::default()`, and the file rendering is the REMAPPED
//     name (`prefer_remapped_unconditionally()`, since WS5.9/WS8.9 — so a sealed identity
//     and every `request_digest` are the same on any machine under
//     `--remap-path-prefix`; the same string as the local name without one) passed through
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
    /// `prefer_local_unconditionally()` verbatim — the SourceMap's own LOCAL name for the
    /// file (the remapped `/rustc/<sha>/…` virtual name only for a decoded sysroot file,
    /// which has no local path). RETIRED from the debug-info lane by WS5.9/WS8.9 (F-117):
    /// it embeds the checkout path in `Module.files`, which every module digest covers, so
    /// module identity became a function of the build directory. Still what the trust-ir
    /// submodule's `frontend/src/span_map.rs` interns until its companion lands; the
    /// consumer keeps it as a FALLBACK lookup for exactly that producer.
    PreferLocalUnconditionally,
    /// `prefer_remapped_unconditionally()` verbatim — the `--remap-path-prefix` rendering,
    /// the only spelling rustc itself permits in a build artifact. REQUIRED for the
    /// debug-info lane since WS5.9/WS8.9: `to_mir.rs::ResolvedFiles` resolves the file by
    /// the same projection against `sm.files()` (refusing, never guessing, when a
    /// non-injective remap makes two files render alike), and DWARF wants the remapped
    /// path. Without a remap it is the same string as the local rendering.
    PreferRemappedUnconditionally,
    /// The REMAPPED rendering wrapped in `trust_types::stable_obligation_file`, which elides
    /// the per-build toolchain token (`/rustc/<sha>/` -> `/rustc/<toolchain>/`). REQUIRED
    /// for the identity lane: without it, `SealedVcIdentity.file` embedded the COMPILER's
    /// commit and every macro-generated obligation's sealed identity moved on each
    /// compiler rebuild. Behaviourally tested in `trust-types/src/model.rs`. The inner
    /// rendering is `prefer_remapped_unconditionally()` (WS5.9/WS8.9, F-117: the
    /// user's checkout path is under neither prefix `stable_obligation_file` elides, so
    /// only the user's own `--remap-path-prefix` can take it out of a sealed identity);
    /// the identity lane must never feed it the LOCAL rendering again — enforced below.
    /// The remapped rendering reaches it through `trust_types::identity_file_rendering`,
    /// which keeps the local rendering ONLY when a remap would mint std or `binary:`
    /// provenance the local path lacks (vcgen reads `SourceSpan.file` as provenance) —
    /// also enforced below: a copy that passes the local rendering any other way, or
    /// drops the guard, is refused.
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
    /// The fingerprints a KNOWN-DEFECT repair of this converter will produce, where one or
    /// more are prescribed (with two independent defects: each repair alone, and both).
    /// Matching one is GREEN: the repair is what this pin wants, and it must not go red at
    /// the moment the repair lands (for a submodule site, that moment is a gitlink bump
    /// whose CI never saw the change). Empty for a site whose `expect` IS the correct
    /// behaviour.
    repaired: &'static [Fingerprint],
    /// Why this fingerprint is what it is — quoted verbatim into any failure.
    rationale: &'static str,
}

/// THE PINNED MATRIX. Six converters in two lanes, one deliberate divergence
/// (`rebases_to_callsite`, plus the lanes' different file renderings) and one still-open
/// defect site (`span_map.rs`: its column, and — since WS5.9/WS8.9 — its local file
/// rendering; each repair fingerprint is pre-accepted, alone and together) — plus two
/// lane-free diagnostic renderings that no decision reads (a zero-authority source readback,
/// and the effect-conservation gate's site text), and one lane-free line-index query that
/// stores no position (SAFETY-ASSUME-1's comment finder), pinned so that none can quietly
/// become a third lane.
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
                file_rendering: FileRendering::PreferRemappedUnconditionally,
            },
            repaired: &[],
            rationale: "CORRECT for its job. Debug-info stamp: callsite-rebased so a \
                        debugger stops at the user's line; LO-only because a DWARF row is a \
                        point; 0-based CharPos verbatim, matching the trust-ir format's \
                        written `; #loc:` contract and the `to_mir.rs::span_from_source_span` \
                        round trip; the REMAPPED file rendering (WS5.9/WS8.9, F-117), because \
                        `Module.files` is digested module content and the checkout path must \
                        not reach it — the round trip resolves it against `sm.files()` by the \
                        same projection (`to_mir.rs::ResolvedFiles`). Reverting this site to \
                        `prefer_local_unconditionally` re-opens F-117 and is REFUSED here.",
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
            // The prescribed repairs — two independent defects, so each alone and both
            // together are pre-accepted: (1) store `CharPos.0` verbatim, per the format's
            // own written contract; (2) intern the REMAPPED file rendering (WS8.9 names
            // this file as needing the same change as `to_source_span`). Landing either
            // in the submodule turns `expect` stale and matches one of these instead —
            // deliberately green, so a repair does not red Trust's suite at gitlink-bump
            // time. Once both land, fold the last one into `expect` and drop this.
            repaired: &[
                Fingerprint {
                    rebases_to_callsite: true,
                    records_hi: false,
                    col_field: ColField::CharPos,
                    col_plus_one: false,
                    dummy_yields_none: true,
                    file_rendering: FileRendering::PreferLocalUnconditionally,
                },
                Fingerprint {
                    rebases_to_callsite: true,
                    records_hi: false,
                    col_field: ColField::ColDisplay,
                    col_plus_one: true,
                    dummy_yields_none: true,
                    file_rendering: FileRendering::PreferRemappedUnconditionally,
                },
                Fingerprint {
                    rebases_to_callsite: true,
                    records_hi: false,
                    col_field: ColField::CharPos,
                    col_plus_one: false,
                    dummy_yields_none: true,
                    file_rendering: FileRendering::PreferRemappedUnconditionally,
                },
            ],
            rationale: "DEFECTIVE COLUMN AND LOCAL FILE RENDERING, KNOWN AND PINNED AS SUCH \
                        (this file is in the \
                        `first-party/trust-ir` submodule, and CLAUDE.md requires cross-repo \
                        changes to go through a separate checkout + a deliberate gitlink \
                        bump — so the repair fingerprint is pre-accepted above rather than \
                        patched here). It writes the SAME type as `to_source_span` but emits \
                        `col_display + 1`, breaking the format contract twice: `col_display` \
                        is a terminal rendering width, and `+ 1` re-bases to 1. Fed to \
                        `to_mir.rs::span_from_source_span` this lands one char right on an \
                        ASCII line, arbitrarily far off on a line with a tab or wide char, \
                        and for the common `shrink_to_hi()` end-of-line stamp overruns to \
                        `chars_in_line + 1`, which fails closed to `None` and drops the span. \
                        And it interns `prefer_local_unconditionally()`, the checkout path, \
                        which WS5.9/WS8.9 retired from the debug-info lane (F-117): the \
                        consumer's local-rendering FALLBACK keeps its modules resolvable \
                        until the companion lands.",
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
            repaired: &[],
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
            repaired: &[],
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
            repaired: &[],
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
            repaired: &[],
            rationale: "The identity lane's OWN LO-only projection; stores no file. \
                        Load-bearing evidence that LO-vs-LO+HI is NOT what blocks \
                        cross-lane comparison — the identity lane already drops HI \
                        wherever it needs a key (here, and in `SealedVcIdentity`). The \
                        callsite rebase is the only irreconcilable axis.",
        },
        // ---- NO LANE: zero-authority diagnostic readback --------------------------------
        Site {
            path: "crates/trust-thir-lower/src/source_static_readback.rs",
            func: "source_json",
            produces: "String (diagnostic JSON in coverage.json; no span value)",
            expect: Fingerprint {
                rebases_to_callsite: false,
                records_hi: true,
                col_field: ColField::CharPos,
                col_plus_one: false,
                dummy_yields_none: false,
                file_rendering: FileRendering::NoneDetected,
            },
            repaired: &[],
            rationale: "NOT A LANE — a zero-authority diagnostic readback (b705ed267c). Its \
                        one coordinate call, `lookup_char_pos(span.lo())`, is used ONLY for \
                        `.file`: to refuse a file with no in-memory `src` (so every decoded \
                        sysroot/extern file is refused, never reopened from disk), to bound \
                        `span.hi()` inside that file, and to read `src_hash`. No `Loc` line \
                        or column is read, so `CharPos` above is this fingerprint's default, \
                        not a measured read. The only stored coordinates are inside rustc's \
                        own `span_to_diagnostic_string`: the RAW span (no callsite rebase), \
                        LO and HI, 1-based `CharPos` columns, the file named at the \
                        DIAGNOSTICS remap scope. Its identity is the SourceFile `src_hash` \
                        plus a domain-separated sha256 of the snippet — content-derived, \
                        free of the `/rustc/<sha>/` build token. A dummy span is a recorded \
                        refusal (`Err`), not `None` and not a default. So it agrees with the \
                        identity lane on the one irreconcilable axis (raw, never rebased) and \
                        with neither lane on column base or file rendering. That is harmless \
                        ONLY because nothing consumes it as a location: the string lands \
                        solely in the opt-in `source_static_readback` key of \
                        `<crate>.coverage.json`, schema-flagged `proof_authority:false` and \
                        `native_verification_requests:false`. No Trust code outside its own \
                        run-make fixture names that key (which asserts only that \
                        `diagnostic` names the file). It is never converted back to a \
                        `Span`, never compared with either lane's values, and never keys an \
                        obligation. Feeding it to a verdict, an identity comparison or a \
                        `Span` round trip would need re-conversion through `convert_span` \
                        or `to_source_span`, and this row does not license that.",
        },
        // ---- NO LANE: refusal-message site text (every decision is made without it) -----
        Site {
            path: "crates/trust-thir-lower/src/effect_conservation.rs",
            func: "render_span",
            produces: "String (`file.rs:line:col` inside a `Tag`'s site text; no span value)",
            expect: Fingerprint {
                rebases_to_callsite: false,
                records_hi: false,
                col_field: ColField::CharPos,
                col_plus_one: true,
                dummy_yields_none: false,
                file_rendering: FileRendering::PreferRemappedUnconditionally,
            },
            repaired: &[],
            rationale: "NOT A LANE — the effect-conservation gate's site text (97de0ab9ac, \
                        reviewed in efe99724a3). Its one coordinate call, \
                        `lookup_char_pos(span.lo())`, reads the RAW span of a MIR statement \
                        or terminator (`source_info.span`, no callsite rebase), the LO edge \
                        only (no `.hi()`), the 1-based line, and `col.0 + 1`: a MEASURED \
                        `CharPos` read re-based to 1, which is rustc's diagnostic convention, \
                        so `col_plus_one` is real. The file is the BASENAME of \
                        `prefer_remapped_unconditionally()`, which the WS5.9/WS8.9 heuristic \
                        detects as `PreferRemappedUnconditionally` (before it the row read \
                        `NoneDetected`, the heuristic's miss, not an absence). The basename drops the `/rustc/<sha>/` build token, but it \
                        also makes distinct files with one name (`mod.rs`, `lib.rs`) \
                        indistinguishable, so the string is not a unique location. A dummy \
                        span yields an empty string (callers then omit ` at …`), not `None`. \
                        So it agrees with the identity lane on the one irreconcilable axis \
                        (raw, never rebased), with both lanes on `CharPos` and an LO point, \
                        and with neither lane on column base or file rendering. That is \
                        harmless ONLY because nothing decides on it. `MirEffect.span` is \
                        read nowhere but here, so effect pairing is span-free. `conserved()` \
                        is `tags.is_empty()`. Codegen admission (`admit_for_codegen`, the F1 \
                        handoff's `withdrawn` map keyed by `FuncId`, \
                        `strip_unconserved_bodies`), strict (a `span_err` anchored at \
                        `def_span`, not at this site), probe channel C and \
                        `admit_for_verification` all decide on tag presence or `TagKind` \
                        alone. The string reaches only message text (`render_tags`, the \
                        trust-cg refusal census's bounded samples, tracing) and the \
                        sidecar's free-text `detail` array. No in-tree reader parses \
                        `detail`: its run-make fixture reads `verdict` and `tags`. It is \
                        never converted back to a `Span`, never compared with either lane's \
                        values, and never keys an obligation, a refusal or a dedup. Keying a \
                        decision on it, or parsing `detail`, would need re-conversion \
                        through `convert_span` or `to_source_span`, and this row does not \
                        license that.",
        },
        // ---- NO LANE: a line-index query that stores no position (SAFETY-ASSUME-1) -------
        Site {
            path: "compiler/rustc_mir_transform/src/trust_verify/safety_comment_assumption.rs",
            func: "comment_above",
            produces: "Option<BytePos> (where a `SAFETY:` comment starts; no line, column or \
                       file is stored)",
            expect: Fingerprint {
                rebases_to_callsite: false,
                records_hi: false,
                col_field: ColField::CharPos,
                col_plus_one: true,
                dummy_yields_none: true,
                file_rendering: FileRendering::NoneDetected,
            },
            repaired: &[],
            rationale: "NOT A LANE — SAFETY-ASSUME-1's comment finder, a port of clippy's \
                        `span_has_safety_comment`. Its two coordinate calls, \
                        `lookup_line(span.lo())` and `lookup_line(body_span.lo())`, ask only \
                        which `SourceFile` and which 0-based line index the unsafe block (or \
                        the statement holding it) and its enclosing fn item start on. \
                        `Arc::ptr_eq` refuses two different files, `body_line.line >= \
                        unsafe_line.line` refuses a block that does not start below the \
                        item's first line, and the two indices slice `sf.lines()` to the \
                        line starts that the text scan reads. No column is read, so \
                        `CharPos` above is this fingerprint's default, not a measured read. \
                        There is no `.hi()` and no file name is rendered. The `+ 1` that sets \
                        `col_plus_one` is a LINE-INDEX bound (`body_line.line + 1`, the \
                        first line below the item's own), not a column re-base. `return \
                        None` means \"no comment found\" (a non-root span, two files, the \
                        wrong order), not a dummy span's location. What it returns is a \
                        `BytePos` (`sf.start_pos` plus the marker's byte offset in `src`), \
                        which `declared_comment` wraps as a zero-width root-context `Span`. \
                        That rustc `Span` reaches a stored position only through \
                        `trust_verify.rs::source_span_from_rustc_span` (the identity-lane \
                        converter pinned above; `safety_comment_charge` calls it) and through \
                        rustc's own `span_note` diagnostic. So no line, column or file this \
                        function reads is stored, compared or keyed on: it decides only \
                        whether a block is DECLARED. Storing its line index, or rendering a \
                        location from `unsafe_line`, would be a new converter, and this row \
                        does not license that.",
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
    "compiler/rustc_mir_transform/src/trust_verify/safety_comment_assumption.rs",
    "crates/trust-mir-extract/src/convert.rs",
    "crates/trust-thir-lower/src/effect_conservation.rs",
    "crates/trust-thir-lower/src/lib.rs",
    "crates/trust-thir-lower/src/source_static_readback.rs",
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
        // WS5.9/WS8.9: the wrapper's INPUT must be the remapped rendering. A copy that
        // wraps the local rendering re-embeds the checkout path in every sealed identity
        // and is classified as the defect it is, not as `RebuildStable`.
        assert!(
            b.contains("prefer_remapped_unconditionally()"),
            "an identity-lane converter feeds `stable_obligation_file` a rendering other than \
             `prefer_remapped_unconditionally()` (F-117: the checkout path would reach every \
             sealed identity and request digest): {b}"
        );
        // WS8.9: the remapped rendering must pass the provenance guard. Without it a
        // `--remap-path-prefix=<co>/src=core/src` makes a user crate's spans read as
        // sysroot std and vcgen deletes their `[unsafe:sep:*]` obligations; and the local
        // rendering may appear ONLY as the guard's fallback argument.
        let normalized = b.replace("trust_types::", "").split_whitespace().collect::<String>();
        assert!(
            normalized.contains(
                "stable_obligation_file(identity_file_rendering(lo.file.name.prefer_local_unconditionally().to_string(),lo.file.name.prefer_remapped_unconditionally().to_string(),))"
            ),
            "an identity-lane converter must render its file as \
             `stable_obligation_file(identity_file_rendering(<local>, <remapped>))` (WS8.9: a \
             remap may erase a path, never mint std/binary provenance): {b}"
        );
        assert_eq!(
            b.matches("prefer_local_unconditionally()").count(),
            1,
            "the local rendering may reach an identity-lane span only as the guard's \
             fallback argument: {b}"
        );
        FileRendering::RebuildStable
    } else if b.contains("prefer_remapped_unconditionally()") {
        FileRendering::PreferRemappedUnconditionally
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
        if site.repaired.contains(&got) {
            // A prescribed repair landed: green by design. Fold it into `expect` on the
            // next deliberate edit of this matrix.
            continue;
        }
        failures.push(format!(
            "\n  {}::{} (-> {})\n    expected: {:?}{}\n    actual:   {:?}\n    \
             pinned because: {}",
            site.path,
            site.func,
            site.produces,
            site.expect,
            if site.repaired.is_empty() {
                String::new()
            } else {
                format!("\n    (also accepted, the repairs: {:?})", site.repaired)
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
    let expected_min = if skipped.is_empty() { 9 } else { 8 };
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
fn the_trusted_std_table_key_is_rendered_like_the_identity_lane() {
    // THE JOIN KEY IS ONE EXPRESSION IN TWO PLACES (WS8.9 review, measured on the
    // 2026-09-22 merge). `trust_mir_extract::trusted_std_source_files` keys the
    // authenticated trusted-std table by a RENDERING of each `SourceFile`'s name, and
    // `sep_engine::is_trusted_std_span` joins that table on `SourceSpan::file`, which the
    // three converters above stamp. The table's VALUE is authenticated (`SourceFile::cnum`
    // plus artifact residency) and no string can forge it — but if the two renderings
    // disagree, every span of a `--remap-path-prefix` build MISSES the table and answers
    // `false`. That is fail-closed, and therefore silent: stdlib's own `unsafe` starts
    // being charged to the user, with no error naming the cause. WS8.9 moved the
    // converters from `prefer_local_unconditionally()` to `identity_file_rendering(local,
    // remapped)` while the table builder, authored on another line, still read the local
    // path; the two changes merged cleanly and produced exactly that. So the invariant the
    // table's own doc comment states ("if those converters ever change their rendering,
    // this one must change with them, and `span_normalization_parity` is the pin that says
    // so") is now actually pinned.
    let repo = repo_root();
    let src = std::fs::read_to_string(repo.join("crates/trust-mir-extract/src/convert.rs"))
        .expect("read trust-mir-extract convert.rs");
    let body = fn_body(&src, "trusted_std_source_files")
        .expect("crates/trust-mir-extract/src/convert.rs: `fn trusted_std_source_files` not found");
    let normalized = strip_line_comments(&body)
        .replace("trust_types::", "")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join("");
    assert!(
        normalized.contains(
            "stable_obligation_file(identity_file_rendering(file.name.prefer_local_unconditionally().to_string(),file.name.prefer_remapped_unconditionally().to_string(),))"
        ),
        "the trusted-std table must key on the SAME rendering the identity-lane converters \
         stamp — `stable_obligation_file(identity_file_rendering(<local>, <remapped>))`. \
         Measured body:\n{normalized}\n"
    );
    // And it must not reach the local path any OTHER way: a bare
    // `prefer_local_unconditionally()` outside the guard is the pre-WS8.9 key.
    assert_eq!(
        normalized.matches("prefer_local_unconditionally()").count(),
        1,
        "exactly one local rendering, and it is the guard's first argument:\n{normalized}\n"
    );
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

/// WS5.9 (F-117): the debug-info ROUND TRIP renders the file name once. The producer
/// (`to_source_span`) interns `prefer_remapped_unconditionally()` into `Module.files`, and
/// the consumer (`to_mir.rs::ResolvedFiles::resolve`, WS8.9's reverse lookup) binds that
/// table back to `sm.files()` under the SAME rendering, tried FIRST, refusing an ambiguous
/// name by name instead of binding the first match.
///
/// This is the increment's mutation control (roadmap WS5.9 "Mutation: revert only the
/// reverse lookup"): reverting ONLY the reverse lookup (a `.find` over
/// `prefer_local_unconditionally()` inside `span_from_source_span`, the pre-WS5.9 shape)
/// leaves every `sites()` fingerprint green — the producer still interns the remapped name
/// — while the round trip silently drops every span of a remapped build. This test fails on
/// exactly that revert.
#[test]
fn debug_info_round_trip_binds_the_interned_rendering() {
    let repo = repo_root();
    const REMAPPED: &str = "prefer_remapped_unconditionally()";
    const LOCAL: &str = "prefer_local_unconditionally()";

    // Producer half: what `Module.files` carries.
    let producer_src = std::fs::read_to_string(repo.join("crates/trust-thir-lower/src/lib.rs"))
        .expect("read trust-thir-lower/src/lib.rs");
    let producer = fn_body(&producer_src, "to_source_span").expect("`fn to_source_span` present");
    assert_eq!(
        fingerprint(&producer).file_rendering,
        FileRendering::PreferRemappedUnconditionally,
        "`to_source_span` must intern the remapped rendering (WS5.9)"
    );

    // Consumer half: the table resolved back against the source map. Scoped to the
    // `impl ResolvedFiles` block, so an unrelated `fn resolve` elsewhere in the file can
    // neither satisfy nor break this pin.
    let consumer_src = std::fs::read_to_string(repo.join("crates/trust-thir-lower/src/to_mir.rs"))
        .expect("read trust-thir-lower/src/to_mir.rs");
    let impl_at = consumer_src.find("impl ResolvedFiles {").unwrap_or_else(|| {
        panic!(
            "to_mir.rs: `impl ResolvedFiles` not found. It is the WS5.9/WS8.9 reverse lookup \
             that binds `Module.files` to `sm.files()` under the remapped rendering; without \
             it a remapped build's spans no longer round-trip to built MIR."
        )
    });
    let impl_src = &consumer_src[impl_at..];
    let resolver = fn_body(impl_src, "resolve").expect("`ResolvedFiles::resolve` present");
    let resolver = strip_line_comments(&resolver);
    let remapped_at = resolver.find(REMAPPED).unwrap_or_else(|| {
        panic!("`ResolvedFiles::resolve` must render `sm.files()` with `{REMAPPED}`")
    });
    if let Some(local_at) = resolver.find(LOCAL) {
        assert!(
            remapped_at < local_at,
            "`ResolvedFiles::resolve` must try the producer's rendering (`{REMAPPED}`) BEFORE \
             the legacy local one; a local-first lookup rebinds a remapped module's names to \
             whatever local file happens to render the same"
        );
    }
    // An ambiguous name is REFUSED by name, never bound to the first match — and the cause
    // is named by what collided (two real files: the remap; a virtual name: not the remap).
    assert!(
        resolver.contains("return unsup(")
            && resolver.contains("Self::NON_INJECTIVE_REMAP")
            && resolver.contains("Self::AMBIGUOUS_VIRTUAL")
            && resolver.contains(".is_real()"),
        "`ResolvedFiles::resolve` must REFUSE an ambiguous module file name, naming \
         `non-injective --remap-path-prefix` for two real files and `ambiguous virtual file \
         name` otherwise, rather than bind the first match"
    );
    let stripped_impl = strip_line_comments(impl_src);
    assert!(
        stripped_impl.contains(
            "const NON_INJECTIVE_REMAP: &'static str = \"non-injective --remap-path-prefix\";"
        ) && stripped_impl
            .contains("const AMBIGUOUS_VIRTUAL: &'static str = \"ambiguous virtual file name\";"),
        "the two refusal causes are pinned texts (the run-make controls and the derived-MIR \
         verdict detail read them)"
    );

    // The per-span lookup no longer renders anything itself: it indexes the resolved table.
    let per_span = fn_body(&consumer_src, "span_from_source_span")
        .expect("`fn span_from_source_span` present");
    let per_span = strip_line_comments(&per_span);
    assert!(
        !per_span.contains(LOCAL) && !per_span.contains(REMAPPED) && !per_span.contains(".find("),
        "`span_from_source_span` must resolve through `ResolvedFiles`, not re-render \
         `sm.files()` per span (the pre-WS5.9 `.find` over `{LOCAL}` bound the FIRST file \
         that rendered to a name, and never the remapped one)"
    );
}

/// WS5.9 (F-117), the anchor row: the rule is every file string that reaches a published
/// module, not `Module.files` alone. A `#[trust::action]` crate also publishes
/// `SpecAnchor.span` (`file:line:col: line:col`), assembled in `crate_module.rs`. Rendered by
/// `SourceMap::span_to_diagnostic_string` — which rustc documents "Must not be emitted to
/// build artifacts" and which follows the DIAGNOSTICS component of `--remap-path-scope` —
/// it embedded the checkout under cargo's `trim-paths` default (`object`) while `files[0]`
/// did not. `embeddable_span_string` renders the same shape with the remapped file name.
///
/// This is the crate-lane control for the run-make row (`trust-ir-remap-path-prefix`,
/// ANCHOR ROW, built under `--remap-path-scope=object`): reverting the anchor row to
/// `span_to_diagnostic_string`, or the helper to the local rendering, fails here without
/// a stage1 build.
#[test]
fn spec_anchor_span_takes_the_remapped_rendering() {
    let repo = repo_root();
    let src = std::fs::read_to_string(repo.join("crates/trust-thir-lower/src/crate_module.rs"))
        .expect("read trust-thir-lower/src/crate_module.rs");
    let helper = fn_body(&src, "embeddable_span_string").unwrap_or_else(|| {
        panic!(
            "crate_module.rs: `fn embeddable_span_string` not found. It is the WS5.9 renderer \
             of `SpecAnchor.span`; without it the anchor row of a temporal crate is spelled by \
             `span_to_diagnostic_string` and embeds the checkout path under \
             `--remap-path-scope=object`."
        )
    });
    let helper = strip_line_comments(&helper);
    assert!(
        helper.contains("prefer_remapped_unconditionally()"),
        "`embeddable_span_string` must render the file `prefer_remapped_unconditionally()` — \
         the one rendering every published file string takes (WS5.9)"
    );
    assert!(
        !helper.contains("prefer_local_unconditionally()")
            && !helper.contains("span_to_diagnostic_string(")
            && !helper.contains("span_to_string("),
        "`embeddable_span_string` must not fall back to a scope- or diagnostics-dependent \
         rendering: those follow `--remap-path-scope` and leak the local checkout"
    );

    // The anchor row itself is assembled by the helper, not by the diagnostics renderer.
    let stripped = strip_line_comments(&src);
    assert!(
        stripped.contains("span: embeddable_span_string(tcx, tcx.def_span(did))"),
        "the `TemporalActionDecl.span` row must be rendered by `embeddable_span_string` (the \
         string reaches the published module as `SpecAnchor.span`)"
    );
    assert!(
        !stripped.contains("span: tcx.sess.source_map().span_to_diagnostic_string("),
        "a module row must not be rendered by `span_to_diagnostic_string` (pre-WS5.9 anchor \
         spelling: rustc documents it as unfit for build artifacts)"
    );
}

/// WS5.9 REVIEW (F-117 residue), the contract-disclosure row: a contract clause the
/// compiler cannot lower is carried as `TrustContractPredicateKind::Unsupported { reason }`,
/// and `trust_thir_lower::contract_disclosure` renders that reason INTO the published module
/// (`{"unsupported":{"reason":...}}` in the contract-disclosure `SpecModule`). When the
/// clause has no source snippet, `trust_contract_query::unsupported_predicate_reason` wrote
/// its location with `span_to_diagnostic_string`, which follows the DIAGNOSTICS component
/// of `--remap-path-scope`: under cargo's `trim-paths` default (`object`) that row kept the
/// checkout path while `Module.files` lost it — the same defect as the anchor row above, in
/// a second module string the increment's "the anchor row was the last" claim missed.
///
/// Mutation control: reverting the location to `span_to_diagnostic_string` (or the helper
/// to the local rendering) fails this test by name.
#[test]
fn unsupported_contract_reason_takes_the_remapped_rendering() {
    let repo = repo_root();
    let path = "compiler/rustc_mir_transform/src/trust_contract_query.rs";
    let src = std::fs::read_to_string(repo.join(path)).expect("read trust_contract_query.rs");

    let reason = fn_body(&src, "unsupported_predicate_reason").unwrap_or_else(|| {
        panic!(
            "{path}: `fn unsupported_predicate_reason` not found. Its text reaches the \
             published module through the contract-disclosure row; if it moved, the new home \
             needs this pin."
        )
    });
    let reason = strip_line_comments(&reason);
    assert!(
        reason.contains("embeddable_span_location(source_map, span)"),
        "`unsupported_predicate_reason` must render the clause location with \
         `embeddable_span_location` — the text is published module content"
    );
    assert!(
        !reason.contains("span_to_diagnostic_string(") && !reason.contains("span_to_string("),
        "`unsupported_predicate_reason` must not render a location with a diagnostics- or \
         scope-dependent renderer: its text is carried into the published module"
    );

    let helper = fn_body(&src, "embeddable_span_location")
        .unwrap_or_else(|| panic!("{path}: `fn embeddable_span_location` not found"));
    let helper = strip_line_comments(&helper);
    assert!(
        helper.contains("prefer_remapped_unconditionally()"),
        "`embeddable_span_location` must render the file `prefer_remapped_unconditionally()` — \
         the one rendering every published file string takes (WS5.9)"
    );
    assert!(
        !helper.contains("prefer_local_unconditionally()")
            && !helper.contains("span_to_diagnostic_string(")
            && !helper.contains("span_to_string("),
        "`embeddable_span_location` must not fall back to a scope- or diagnostics-dependent \
         rendering: those follow `--remap-path-scope` and leak the local checkout"
    );
}

/// WS5.9 / WS5.23 landing review (2026-09-28): the two module-content location renderers —
/// `crate_module.rs::embeddable_span_string` (`SpecAnchor.span`) and
/// `trust_contract_query.rs::embeddable_span_location` (the contract-disclosure
/// `Unsupported` reason) — are "rendering only" because each is
/// `SourceMap::span_to_diagnostic_string`'s own SHAPE with only the FILE rendering changed:
/// the same `span_to_location_info` fields (1-based columns), the same
/// `file:line:col: line:col` format, the same `no-location` fallback. The two pins above
/// check the file rendering; this one checks the shape, against rustc_span's own
/// `span_to_string_ext` in THIS tree, so a drift on either side — rustc reshaping its
/// diagnostic string, or a helper reshaping its copy — fails here by name instead of
/// silently moving every published anchor.
#[test]
fn embeddable_span_renderers_keep_the_diagnostic_shape() {
    let repo = repo_root();
    let squash =
        |src: &str| strip_line_comments(src).split_whitespace().collect::<Vec<_>>().join(" ");
    let read = |path: &str| {
        std::fs::read_to_string(repo.join(path)).unwrap_or_else(|e| panic!("read {path}: {e}"))
    };

    // Upstream: what `span_to_diagnostic_string` renders.
    let rustc = read("compiler/rustc_span/src/source_map.rs");
    let body = |src: &str, name: &str| {
        squash(&fn_body(src, name).unwrap_or_else(|| panic!("`fn {name}` not found")))
    };
    let diagnostic = body(&rustc, "span_to_diagnostic_string");
    assert!(
        diagnostic.contains("self.span_to_string(sp, RemapPathScopeComponents::DIAGNOSTICS)"),
        "rustc_span: `span_to_diagnostic_string` no longer renders through `span_to_string` at \
         the DIAGNOSTICS scope; re-derive the helpers' shape. Body: {diagnostic}"
    );
    let long = body(&rustc, "span_to_string");
    assert!(
        long.contains("self.span_to_string_ext(sp, display_scope, false)"),
        "rustc_span: `span_to_string` no longer renders the LONG shape; body: {long}"
    );
    let ext = body(&rustc, "span_to_string_ext");
    for needle in [
        "let (source_file, lo_line, lo_col, hi_line, hi_col) = self.span_to_location_info(sp);",
        "None => return \"no-location\".to_string(),",
        "\"{file_name}:{lo_line}:{lo_col}{}\"",
        "format!(\": {hi_line}:{hi_col}\")",
    ] {
        assert!(
            ext.contains(needle),
            "rustc_span: `span_to_string_ext` changed shape (missing `{needle}`); the embeddable \
             helpers copy that shape and must move with it. Body: {ext}"
        );
    }

    // Ours: the same fields, the same format, the same fallback; only the file differs.
    for (path, name, receiver) in [
        (
            "crates/trust-thir-lower/src/crate_module.rs",
            "embeddable_span_string",
            "tcx.sess.source_map()",
        ),
        (
            "compiler/rustc_mir_transform/src/trust_contract_query.rs",
            "embeddable_span_location",
            "source_map",
        ),
    ] {
        let helper = body(&read(path), name);
        for needle in [
            format!(
                "let (source_file, lo_line, lo_col, hi_line, hi_col) = \
                 {receiver}.span_to_location_info(span);"
            ),
            "Some(sf) => format!( \"{}:{lo_line}:{lo_col}: {hi_line}:{hi_col}\", \
             sf.name.prefer_remapped_unconditionally() ),"
                .to_string(),
            "None => \"no-location\".to_string(),".to_string(),
        ] {
            assert!(
                helper.contains(&needle),
                "{path}: `{name}` is not `span_to_diagnostic_string`'s shape with the file \
                 rendered `prefer_remapped_unconditionally()` (missing `{needle}`). Body: {helper}"
            );
        }
    }
}
