// trust_vcgen/unsafe_verify/detection.rs: Unsafe block detection and safety comment parsing
//
// Detects unsafe blocks in MIR, extracts // SAFETY: comments from source spans,
// parses structured safety claims, and generates Assertion VCs that encode the
// claimed invariants.
//
// Part of #79, #137: Unsafe code verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_types::fx::FxHashSet;

use super::{SafetyClaim, UnsafeBlock};

/// Detect unsafe blocks in a verifiable function.
///
/// In MIR, unsafe blocks manifest as Call terminators to functions that require
/// unsafe (e.g., `ptr::read`, `ptr::write`, `slice::from_raw_parts`), or
/// as blocks containing raw pointer dereferences (Deref projections on raw ptrs).
///
/// We also detect explicit unsafe annotations via the function's contracts
/// and trust annotations.
#[must_use]
pub(crate) fn detect_unsafe_blocks(func: &VerifiableFunction) -> Vec<UnsafeBlock> {
    let mut blocks = Vec::new();

    for block in &func.body.blocks {
        // Check for unsafe calls in the terminator. `is_unsafe_sig` (T5A) is
        // the AUTHORITATIVE signal — rustc's fn-signature safety recorded at
        // extraction — and `is_foreign` is the authoritative FFI signal
        // (round-19 #3); both are serde-default-false. The name heuristic
        // `is_unsafe_fn_call` is retained ONLY as a fallback for synthetic /
        // test MIR (and old serialized MIR) that predates the flags: dropping
        // it would silently un-detect every existing synthetic fixture. It can
        // only ADD blocks (over-approximation is a doc-lint demand, never a
        // proof), so keeping it cannot mask a missed authoritative signal.
        if let Terminator::Call { func: callee, span, is_unsafe_sig, is_foreign, .. } =
            &block.terminator
            && (*is_unsafe_sig || *is_foreign || is_unsafe_fn_call(callee))
        {
            blocks.push(UnsafeBlock {
                span: span.clone(),
                safety_comment: None,
                safety_claim: None,
                block_id: block.id,
            });
        }

        // Check for raw pointer dereferences in statements
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && has_raw_deref(func, rvalue)
            {
                blocks.push(UnsafeBlock {
                    span: span.clone(),
                    safety_comment: None,
                    safety_claim: None,
                    block_id: block.id,
                });
            }
        }
    }

    blocks
}

/// Attach safety comments to detected unsafe blocks.
///
/// In a full compiler integration, comments would come from the source map.
/// This function accepts pre-extracted comment text and matches them to blocks
/// by source span proximity.
pub(crate) fn attach_safety_comments(
    blocks: &mut [UnsafeBlock],
    comments: &[(SourceSpan, String)],
) {
    for block in blocks.iter_mut() {
        // Select the closest preceding recognized SAFETY comment independently
        // of input order. Equal-distance comments use a stable source/text key,
        // so callers cannot change the attached claim merely by permuting the
        // compiler-owned comment list.
        let closest = comments
            .iter()
            .filter(|(comment_span, text)| {
                comment_span.file == block.span.file
                    && comment_span.line_end <= block.span.line_start
                    && block.span.line_start - comment_span.line_end <= 2
                    && comment_has_safety_line(text)
            })
            .min_by_key(|(comment_span, text)| {
                (
                    block.span.line_start - comment_span.line_end,
                    std::cmp::Reverse(comment_span.line_start),
                    std::cmp::Reverse(comment_span.col_start),
                    comment_span.line_end,
                    comment_span.col_end,
                    text.as_str(),
                )
            });
        if let Some((_, text)) = closest {
            block.safety_comment = Some(text.clone());
            block.safety_claim = Some(parse_safety_comment(text));
        }
    }
}

/// Normalize one source-comment line for the shared SAFETY grammar.
///
/// Matching and parsing must use this same normalization: accepting a comment
/// at attachment time that the parser interprets as ordinary prose can silently
/// change which follow-up null/alignment obligations are generated.
fn normalized_comment_line(line: &str) -> &str {
    let mut line = line.trim();
    if let Some(rest) = line.strip_prefix("//") {
        line = rest.trim();
    } else if let Some(rest) = line.strip_prefix("/*") {
        line = rest.trim();
    } else if let Some(rest) = line.strip_prefix('*') {
        line = rest.trim();
    }
    if let Some(rest) = line.strip_suffix("*/") {
        line = rest.trim();
    }
    line
}

/// Return the claim payload when `line` begins with the one recognized SAFETY
/// marker grammar. Embedded prose such as `mentions SAFETY: elsewhere` is not a
/// declaration and therefore fails closed.
fn safety_line_payload(line: &str) -> Option<&str> {
    let line = normalized_comment_line(line);
    line.strip_prefix("SAFETY:").or_else(|| line.strip_prefix("SAFETY :")).map(str::trim)
}

fn comment_has_safety_line(comment: &str) -> bool {
    comment.lines().any(|line| safety_line_payload(line).is_some())
}

/// Parse a `// SAFETY:` comment into a structured safety claim.
///
/// Expected format:
/// ```text
/// // SAFETY: <invariant>
/// // <justification>
/// ```
///
/// Or single-line:
/// ```text
/// // SAFETY: <invariant> because <justification>
/// ```
///
/// If only the invariant line is present, justification defaults to
/// "no justification provided".
#[must_use]
pub(crate) fn parse_safety_comment(comment: &str) -> SafetyClaim {
    // Strip comment markers and find the SAFETY: prefix
    let lines: Vec<&str> =
        comment.lines().map(normalized_comment_line).filter(|line| !line.is_empty()).collect();

    if lines.is_empty() {
        return SafetyClaim {
            invariant: String::new(),
            justification: "no justification provided".to_string(),
        };
    }

    // Find the line with SAFETY:
    let safety_idx = lines.iter().position(|line| safety_line_payload(line).is_some());

    let safety_line = match safety_idx {
        Some(idx) => lines[idx],
        None => {
            // No SAFETY: prefix found, treat entire comment as invariant
            return SafetyClaim {
                invariant: lines.join(" "),
                justification: "no justification provided".to_string(),
            };
        }
    };

    // Extract the invariant (text after "SAFETY:")
    let after_safety = safety_line_payload(safety_line).unwrap_or_default();

    // Check for "because" separator in single-line format
    if let Some(because_idx) = after_safety.to_lowercase().find(" because ") {
        let invariant = after_safety[..because_idx].trim().to_string();
        let justification = after_safety[because_idx + 9..].trim().to_string();
        return SafetyClaim { invariant, justification };
    }

    let invariant = after_safety.to_string();

    // Justification is the remaining lines after the SAFETY: line
    let justification_lines: Vec<&str> = match safety_idx {
        Some(idx) => lines[idx + 1..].to_vec(),
        None => vec![],
    };

    let justification = if justification_lines.is_empty() {
        "no justification provided".to_string()
    } else {
        justification_lines.join(" ")
    };

    SafetyClaim { invariant, justification }
}

/// Generate verification conditions for unsafe blocks.
///
/// For each unsafe block with a parsed safety claim, we generate an Assertion
/// VC encoding the invariant. Unsafe blocks without safety comments get a
/// "missing SAFETY comment" assertion that is trivially satisfiable (always
/// a finding).
///
/// The convention is: Assertion VCs with `message` prefixed by `[unsafe]`
/// are from unsafe verification. This lets reporters distinguish them.
/// Peel `&`/`&mut` layers off a type to reach the pointee.
fn peel_refs(mut ty: Ty) -> Ty {
    loop {
        match ty {
            Ty::Ref { inner, .. } => ty = *inner,
            other => return other,
        }
    }
}

/// True iff MIR block `block_id` is terminated by a SCALAR-index slice
/// `get_unchecked` / `get_unchecked_mut` call — the ONE unsafe shape whose
/// COMPLETE undefined-behavior set is exactly `index < len`: a valid
/// `&[T]`/`&mut [T]` receiver is non-null / aligned / valid-provenance by typing,
/// and a `usize` index rules out the range form (`get_unchecked(a..b)`), whose
/// precondition is instead `a <= b <= len`. For exactly this shape the separation
/// engine emits a real, discharge-able `VcKind::IndexOutOfBounds` obligation
/// (`index >= len`, sep_engine.rs), so the always-`Bool(true)` "missing SAFETY
/// comment" DOCUMENTATION lint is redundant and is suppressed for THIS block.
///
/// SOUNDNESS — keyed on the block's OWN terminator identity, never on span
/// co-location: a raw pointer `Deref`, `from_raw_parts`, `transmute`, or a
/// blanket-only unsafe call like `mem::zeroed` lives in its OWN MIR block (its own
/// terminator/statement), so it is a DIFFERENT `UnsafeBlock` and keeps its
/// fail-closed lint even if the source span byte-collides (e.g. proc-macro
/// `Span::call_site()`). Fails closed on every non-matching shape (unknown block,
/// non-Call terminator, non-`get_unchecked` callee, non-scalar index, non-slice
/// receiver) → the lint is retained.
fn block_is_bounds_complete_unchecked_index(func: &VerifiableFunction, block_id: BlockId) -> bool {
    let Some(mir) = func.body.blocks.iter().find(|b| b.id == block_id) else {
        return false;
    };
    let Terminator::Call { func: callee, args, .. } = &mir.terminator else {
        return false;
    };
    if !callee.contains("::get_unchecked") || args.len() < 2 {
        return false;
    }
    // Index must be a SCALAR integer (`usize`). A range index (`a..b`) is a
    // struct — NOT `Ty::Int` — and carries a different precondition, so it fails
    // this gate and keeps its fail-closed lint.
    if !matches!(crate::operand_ty(func, &args[1]), Some(Ty::Int { .. })) {
        return false;
    }
    // Receiver (behind any refs) must be a slice/array, so `len` is its element
    // count. Anything else (e.g. `str`) fails closed.
    matches!(
        crate::operand_ty(func, &args[0]).map(peel_refs),
        Some(Ty::Slice { .. } | Ty::Array { .. })
    )
}

pub(crate) fn generate_safety_vcs(
    func: &VerifiableFunction,
    blocks: &[UnsafeBlock],
    box_deref_spans: &FxHashSet<SourceSpan>,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for block in blocks {
        // SOURCE-LEVEL SCOPING: the SAFETY-comment obligations below are a
        // *source-documentation* lint (always `Bool(true)` — they verify no
        // behavioral property, only that the author documented their reasoning).
        // After inlining, a callee's unsafe block (e.g. std's
        // `box_assume_init_into_vec_unsafe`, which `vec!` expands to) appears in
        // THIS function's post-inline MIR with a span pointing at the callee's
        // own source file. Charging the caller a "missing SAFETY comment" for code
        // it did not write is a category error — that obligation belongs to the
        // function that syntactically CONTAINS the block. Skip blocks whose span
        // is in a different source file than the function under verification. This
        // loses NO behavioral coverage: the inlined operations' real safety (raw
        // deref non-null/aligned, union-field reads) is still checked by the
        // panic-boundary asserts and the union/static obligations, which are not
        // filtered here. (When either file is unknown/empty we keep the block —
        // conservative.)
        if !block.span.file.is_empty()
            && !func.span.file.is_empty()
            && block.span.file != func.span.file
        {
            continue;
        }
        // TRUSTED-STD-SPAN SCOPING (companion to the different-file skip above): a
        // compiler/std-macro-generated unsafe block whose OWN span resolves to the
        // sysroot standard library is code the user did NOT write and CANNOT
        // annotate, so charging them a "missing SAFETY comment" (or tracking std's
        // own SAFETY claim) is the SAME category error. The different-file skip
        // misses the case where the WHOLE function under verification is
        // macro-generated — e.g. the `thread_local!` expansion's `unsafe { … }`
        // closures `rational::ARENA::{constant#0}::{closure#0,1}`, whose span AND
        // the closure's own span both point at `library/std/src/sys/thread_local/
        // native/mod.rs`, so `block.span.file == func.span.file` and the skip above
        // does not fire. Reuse the vetted `sep_engine::is_trusted_std_span` — the
        // SAME predicate the behavioral unsafe-op VCs already skip on
        // (sep_engine.rs) — so no new trust surface is introduced. FAIL-CLOSED and
        // SOUND: it returns `true` ONLY for a positively-identified sysroot std
        // path; a genuine ny-cert `unsafe` block resolves to a first-party path and
        // is NEVER exempted (keeps its lint). Loses NO behavioral coverage: the real
        // safety (raw deref non-null/aligned, union-field, mutable/extern static) is
        // checked by separate obligations that likewise skip std spans.
        if crate::sep_engine::is_trusted_std_span(&block.span) {
            // Env-gated decision-point trace (`TRUST_TLS_DISCHARGE_DEBUG=1`).
            if std::env::var_os("TRUST_TLS_DISCHARGE_DEBUG").is_some() {
                eprintln!(
                    "TRUST_TLS_DISCHARGE_DEBUG: skipping SAFETY-comment lint for \
                     std-macro-generated unsafe block @ {} in `{}` — user-un-annotatable; \
                     behavioral safety checked by separate std-span-skipping obligations",
                    block.span.file,
                    func.name.as_str()
                );
            }
            continue;
        }
        match &block.safety_claim {
            Some(claim) if !claim.invariant.is_empty() => {
                // Generate a conservative VC for the claimed invariant.
                //
                // SOUNDNESS FIX: The old code used an unconstrained
                // boolean variable `safety_invariant_N` wrapped in Not().
                // The solver could set it to true, making Not(true) = UNSAT,
                // which vacuously "proved" every safety claim without checking
                // anything. We now use Formula::Bool(true) as the violation
                // formula — always SAT — meaning this VC conservatively
                // reports "cannot mechanically verify this claim" unless
                // downstream analysis constrains it further.
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe] SAFETY claim (unverified): {}",
                            claim.invariant,
                        ),
                    },
                    function: func.name.as_str().into(),
                    location: block.span.clone(),
                    // Always SAT = conservatively "cannot verify".
                    // A downstream pass with actual program constraints can
                    // strengthen this into a real check.
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                });

                // If the justification references nullability, generate
                // a non-null check VC.
                if claim.invariant.to_lowercase().contains("non-null")
                    || claim.invariant.to_lowercase().contains("not null")
                    || claim.invariant.to_lowercase().contains("nonnull")
                {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe] null pointer check for: {}",
                                claim.invariant,
                            ),
                        },
                        function: func.name.as_str().into(),
                        location: block.span.clone(),
                        formula: Formula::Eq(
                            Box::new(Formula::Var(
                                super::generated_unsafe_symbol(&format!(
                                    "claim_ptr_bb{}",
                                    block.block_id.0
                                )),
                                Sort::Int,
                            )),
                            Box::new(Formula::Int(0)),
                        ),
                        contract_metadata: None,
                        obligation: None,
                    });
                }

                // If the justification references alignment, generate
                // an alignment check VC.
                if claim.invariant.to_lowercase().contains("align") {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe] alignment check (unverified) for: {}",
                                claim.invariant,
                            ),
                        },
                        function: func.name.as_str().into(),
                        location: block.span.clone(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                        obligation: None,
                    });
                }
            }
            _ => {
                // Trust (box-deref doc-lint fix): drop the always-`Bool(true)`
                // missing-SAFETY doc lint for a raw deref of a COMPILER-SYNTHESIZED
                // Box pointer (ElaborateBoxDerefs / box drop-glue Transmute of a
                // Box's Unique.NonNull field), whose span the compiler collected.
                // DROP-ONLY: the deref's real non-null/aligned validity is still
                // checked by synthetic_nonmodeled_unsafe_op_vcs (not filtered here).
                // Excludes first-party mem::transmute-of-NonNull derefs (bare NonNull
                // source, never collected). The cross-file guard above catches
                // inlined CALLEE-file unsafe; this catches the box deref whose span
                // is the caller's OWN token (same file → the file guard misses it).
                if box_deref_spans.contains(&block.span) {
                    continue;
                }

                // OP-IDENTITY SUPERSESSION (sound): a scalar-index slice
                // `get_unchecked` block's COMPLETE UB set is exactly `index < len`,
                // for which the separation engine emits a real, discharge-able
                // `VcKind::IndexOutOfBounds` obligation. That real obligation
                // supersedes this always-`Bool(true)` documentation-only lint for
                // THIS block. Keyed on the block's own terminator identity (NOT span
                // co-location), so a co-located/inlined non-bounds unsafe op — which
                // occupies its own MIR block — keeps its fail-closed lint. An
                // UNGUARDED index still fails on the real `index >= len` obligation.
                if block_is_bounds_complete_unchecked_index(func, block.block_id) {
                    continue;
                }

                // No dependency-tracked safety claim was attached: generate a
                // "missing comment" assertion. Do not reopen `span.file` through
                // cwd/CARGO_MANIFEST_DIR here; those ambient bytes are outside
                // rustc's source dependency graph and previously could suppress
                // this obligation with a same-named or edited file.
                // This is always SAT (Bool(true)) = always a finding.
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: "[unsafe] missing SAFETY comment on unsafe block".to_string(),
                    },
                    function: func.name.as_str().into(),
                    location: block.span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                });
            }
        }
    }

    vcs
}

/// COMPLETENESS (fail-closed): inline assembly is unconditionally unsafe and can
/// cause arbitrary undefined behavior, but it is extracted as a
/// `Terminator::Opaque` (kind `"InlineAsm"`) that the rest of the pipeline does
/// not model — so without this it would be SILENTLY ignored (an unverified hole,
/// the exact kind of "other" that must not exist). Emit an always-finding
/// obligation for each inline-asm terminator so it is CAUGHT under the default
/// strict policy, never silently passed. Trust has no semantic model of
/// arbitrary asm, so this is fail-closed by design until a specific asm model is
/// added. Runs independently of `has_intrinsic_unsafe_surface` because an
/// asm-only function has no other unsafe surface to trip that gate.
pub(crate) fn generate_inline_asm_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    for block in &func.body.blocks {
        if let Terminator::Opaque { kind, span, .. } = &block.terminator
            && kind.contains("InlineAsm")
        {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: "[unsafe:asm] inline assembly is not modeled — cannot prove \
                              memory-safe (fail-closed)"
                        .to_string(),
                },
                function: func.name.as_str().into(),
                location: span.clone(),
                // Always SAT = always a finding: no model of asm semantics exists.
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            });
        }
    }
    vcs
}

/// Check whether a function call name refers to an inherently unsafe function.
pub(crate) fn is_unsafe_fn_call(callee: &str) -> bool {
    const UNSAFE_PATTERNS: &[&str] = &[
        // Core pointer operations
        "ptr::read",
        "ptr::write",
        "ptr::read_volatile",
        "ptr::write_volatile",
        "ptr::copy",
        "ptr::copy_nonoverlapping",
        "ptr::swap",
        "ptr::replace",
        "ptr::drop_in_place",
        "ptr::read_unaligned",
        "ptr::write_unaligned",
        // Slice from raw parts
        "slice::from_raw_parts",
        "slice::from_raw_parts_mut",
        // String from raw
        "str::from_utf8_unchecked",
        "String::from_raw_parts",
        // Transmute
        "mem::transmute",
        "mem::transmute_copy",
        "mem::zeroed",
        "mem::uninitialized",
        // Alloc
        "alloc::alloc",
        "alloc::dealloc",
        "alloc::realloc",
        // Unchecked indexing and uninit reads — MODELED by sep_engine
        // (`is_unchecked_index_call` / `unsafe_assertion_op`) but previously
        // absent here, so a block whose ONLY unsafe op was one of these escaped
        // unsafe-block detection. `get_unchecked` covers `get_unchecked_mut`.
        "get_unchecked",
        "assume_init",
        // Other well-known unsafe std operations (broaden heuristic coverage).
        "set_len",                       // Vec::set_len / String/etc.
        "new_unchecked",                 // NonNull::new_unchecked, NonZero*, …
        "unreachable_unchecked",         // core::hint::unreachable_unchecked
        "from_u32_unchecked",            // char::from_u32_unchecked
        "from_bytes_with_nul_unchecked", // CStr
        // Intrinsics
        "intrinsics::",
        // T5A: the "::ffi::" NAMESPACE entry was deleted. Every other pattern
        // here names a genuinely-unsafe FN; "::ffi::" matched a MODULE path and
        // so flagged SAFE std::ffi calls (`OsStr::to_str`, `OsString::push`,
        // `env::vars_os` glue, …), demanding SAFETY comments on safe code
        // (aterm-uds 4, aterm-types 2, aterm-pty up to 29 false demands).
        // Genuinely unsafe calls under ::ffi:: (`CStr::from_ptr`, …) are still
        // detected — authoritatively — via `Terminator::Call::is_unsafe_sig`,
        // and genuine FFI imports via `is_foreign`.
    ];

    let lower = callee.to_lowercase();
    UNSAFE_PATTERNS.iter().any(|p| lower.contains(&p.to_lowercase()))
}

/// Check whether an rvalue contains a raw pointer dereference.
pub(crate) fn has_raw_deref(func: &VerifiableFunction, rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(operand) => crate::operand_has_raw_deref(func, operand),
        Rvalue::Ref { place, .. } | Rvalue::CopyForDeref(place) => {
            crate::place_has_raw_deref(func, place)
        }
        _ => false,
    }
}
