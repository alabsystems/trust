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

use trust_types::fx::FxHashSet;
use trust_types::*;

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
        let call = match &block.terminator {
            Terminator::Call { func, span, is_unsafe_sig, is_foreign, .. }
            | Terminator::TailCall { func, span, is_unsafe_sig, is_foreign, .. } => {
                Some((func, span, *is_unsafe_sig, *is_foreign))
            }
            _ => None,
        };
        if let Some((callee, span, is_unsafe_sig, is_foreign)) = call
            && (is_unsafe_sig || is_foreign || is_unsafe_fn_call(callee))
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
/// comment" stand-in row is redundant and is suppressed for THIS block.
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
    let (callee, args) = match &mir.terminator {
        Terminator::Call { func, args, .. } | Terminator::TailCall { func, args, .. } => {
            (func, args)
        }
        _ => return false,
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

/// Generate the per-unsafe-block obligations.
///
/// NOT the documentation lint its message names — it never reads documentation.
/// MEASURED (stage2 b1254a567, same crate with and without `// SAFETY:` on each
/// block: byte-identical obligation set, message still "missing SAFETY comment"):
/// the ONLY production caller is `check_unsafe(func, &[], …)` in
/// `generate::entry` — vcgen has no source-map access, so `comments` is ALWAYS
/// empty, `safety_claim` is ALWAYS `None`, and the `_` arm fires for EVERY
/// detected block. The `Some(claim)` arms are reachable only from
/// `unsafe_verify::verifier`, which is test-only.
///
/// What it actually is in production: an unconditional always-`Bool(true)`
/// fail-closed demand, one per detected unsafe block. It is LOAD-BEARING —
/// MEASURED, for the blanket-only unsafe ops (`mem::zeroed`,
/// `mem::uninitialized`, `hint::unreachable_unchecked`) it is the SOLE unsafe
/// obligation: `call_is_modeled` suppresses their `[unsafe:unmodeled-call]` row
/// and the separation engine mints none. Dropping it from L0 is a fail-open.
/// Making the message honest requires SAFETY comments plumbed from the
/// compiler's source map, which is a change outside this crate.
///
/// Convention: `Assertion`s whose message starts `[unsafe` are the unsafe
/// family. `VcKind::hardened_category` maps them to `UnsafeOperation`, and
/// `refute_unsafe_demand_findings` (rustc_mir_transform/trust_verify.rs) forces
/// every one of them `Failed` — which is what keeps `VcKind::Assertion`'s
/// blanket `has_runtime_fallback == true` from ever reaching
/// `classify_runtime_disposition` for these rows.
pub(crate) fn generate_safety_vcs(
    func: &VerifiableFunction,
    blocks: &[UnsafeBlock],
    box_deref_spans: &FxHashSet<SourceSpan>,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for block in blocks {
        // SOURCE-LEVEL SCOPING: the obligations below are always `Bool(true)` and
        // verify no behavioral property; the block's own operation is what they
        // stand in for. After inlining, a callee's unsafe block (e.g. std's
        // `box_assume_init_into_vec_unsafe`, which `vec!` expands to) appears in
        // THIS function's post-inline MIR with a span pointing at the callee's
        // own source file. Charging the caller a "missing SAFETY comment" for code
        // it did not write is a category error — that obligation belongs to the
        // function that syntactically CONTAINS the block. Skip blocks whose span
        // is in a different source file than the function under verification.
        //
        // UNVERIFIED (do not repeat as fact): this skip used to claim it "loses NO
        // behavioral coverage" because raw-deref/union safety has its own rows.
        // That holds for the ops that DO have their own rows, and NOT for the
        // blanket-only class (`mem::zeroed`, `mem::uninitialized`,
        // `hint::unreachable_unchecked`), for which the row dropped here is the
        // SOLE obligation — see this function's doc comment. A cross-file
        // blanket-only block was NOT reproduced (attempted: `vec!` and
        // `MaybeUninit::assume_init` on stage2 b1254a567 — vcgen sees pre-inline
        // MIR there, so both callees stayed calls and this skip never fired), so
        // no fail-open is claimed; the coverage argument is simply not
        // established for that class. (Unknown/empty file keeps the block.)
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
        // does not fire. Reuse the vetted `sep_engine::is_trusted_std_span`
        // provenance predicate, so no new path-recognition trust surface is
        // introduced. FAIL-CLOSED and SOUND: it returns `true` ONLY for a
        // positively-identified sysroot std path; a genuine ny-cert `unsafe`
        // block resolves to a first-party path and is NEVER exempted (keeps its
        // row). Carries the SAME unverified coverage claim as the different-file
        // skip above — raw-deref/union/static safety do have their own rows, the
        // blanket-only class does not — so read that note before widening this.
        if crate::sep_engine::is_trusted_std_span(&block.span) {
            // Env-gated decision-point trace (`TRUST_TLS_DISCHARGE_DEBUG=1`).
            if std::env::var_os("TRUST_TLS_DISCHARGE_DEBUG").is_some() {
                eprintln!(
                    "TRUST_TLS_DISCHARGE_DEBUG: skipping SAFETY-comment lint for \
                     std-macro-generated unsafe block @ {} in `{}` — user-un-annotatable; \
                     behavioral safety handled by separate owner-scoped obligations",
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
                // supersedes this always-`Bool(true)` stand-in row for THIS block.
                // Keyed on the block's own terminator identity (NOT span
                // co-location), so a co-located/inlined non-bounds unsafe op — which
                // occupies its own MIR block — keeps its fail-closed row. An
                // UNGUARDED index still fails on the real `index >= len` obligation.
                if block_is_bounds_complete_unchecked_index(func, block.block_id) {
                    continue;
                }

                // THE production arm — no safety claim was attached, and in
                // production none ever is (see this function's doc comment), so
                // the message is false whenever the block IS documented. Do not
                // "fix" it by reopening `span.file` through cwd/CARGO_MANIFEST_DIR:
                // those ambient bytes are outside rustc's source dependency graph
                // and previously suppressed this obligation via a same-named or
                // edited file. Always SAT (`Bool(true)`) = always a finding, and
                // for a blanket-only unsafe op it is the only one.
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

/// Does `callee` name an item under `{core,std}::intrinsics::`, and if so what
/// is its DIRECT leaf name?
///
/// * `None` — not an intrinsics-module path at all.
/// * `Some(None)` — under the module, but not a direct child: the SIMD family
///   (`core::intrinsics::simd::simd_add`) and the custom-MIR DSL
///   (`core::intrinsics::mir::*`). The caller fails closed on these.
/// * `Some(Some(leaf))` — a direct child, leaf name with generic args stripped.
///
/// Accepts the three spellings the pipeline actually produces:
///
/// * `core::intrinsics::ctpop` — the plain extracted def path,
/// * `core::intrinsics::ctpop::<u32>` — with the instantiated generic args,
/// * `@trust-rustc-intrinsic::core::intrinsics::ctpop::<u32>` — the extractor's
///   authenticated intrinsic marker (`TRUST_RUSTC_INTRINSIC_PATH_PREFIX`).
fn core_intrinsics_leaf(callee: &str) -> Option<Option<&str>> {
    // The module qualifier is spelled `core::` in a `no_std` extraction and
    // `std::` through the facade; both reach the same items.
    let after = ["core::intrinsics::", "std::intrinsics::"]
        .iter()
        .find_map(|prefix| callee.find(prefix).map(|at| &callee[at + prefix.len()..]))?;
    // `ctpop::<u32>` -> `ctpop`; `simd::simd_add` -> not a direct child.
    let leaf = match after.split_once("::") {
        None => after,
        Some((head, rest)) if rest.starts_with('<') => head,
        Some(_) => return Some(None),
    };
    // A def path never carries a bare `<` outside the `::<…>` args form, but
    // stay total for synthetic / hand-written fixture names.
    let leaf = leaf.split('<').next().unwrap_or(leaf);
    Some(if leaf.is_empty() { None } else { Some(leaf) })
}

/// The intrinsics whose `library/core` declaration is a SAFE `fn` — i.e. the
/// exact set for which `tcx.fn_sig(..).safety()` is `Safety::Safe`, and
/// therefore for which `Terminator::Call::is_unsafe_sig` is authoritatively
/// `false`.
///
/// TRANSCRIBED MECHANICALLY from this tree's `library/core/src/intrinsics/mod.rs`:
/// every `#[rustc_intrinsic]` item declared without `unsafe`, plus the two safe
/// non-intrinsic helpers that live in the same module (`likely`, `unlikely` —
/// whose own doc comment says *"unlike most intrinsics, this is safe to call;
/// it does not require an `unsafe` block"*). Regenerate with the same rule if
/// `library/core` gains intrinsics; a name MISSING from this list is treated as
/// unsafe (fail-closed), so drift can only ever cost signal, never an
/// obligation.
///
/// Sorted — [`is_safe_core_intrinsic`] binary-searches it, and
/// `safe_core_intrinsics_table_is_sorted` pins the ordering.
const SAFE_CORE_INTRINSICS: &[&str] = &[
    "abort",
    "add_with_overflow",
    "aggregate_raw_ptr",
    "align_of",
    "assert_inhabited",
    "assert_mem_uninitialized_valid",
    "assert_zero_valid",
    "autodiff",
    "bitreverse",
    "black_box",
    "breakpoint",
    "bswap",
    "caller_location",
    "carrying_mul_add",
    "carryless_mul",
    "ceilf128",
    "ceilf16",
    "ceilf32",
    "ceilf64",
    "cold_path",
    "const_eval_select",
    "contract_check_ensures",
    "contract_check_requires",
    "copysignf128",
    "copysignf16",
    "copysignf32",
    "copysignf64",
    "cosf128",
    "cosf16",
    "cosf32",
    "cosf64",
    "ctlz",
    "ctpop",
    "cttz",
    "discriminant_value",
    "exp2f128",
    "exp2f16",
    "exp2f32",
    "exp2f64",
    "expf128",
    "expf16",
    "expf32",
    "expf64",
    "fabs",
    "fadd_algebraic",
    "fdiv_algebraic",
    "field_offset",
    "field_representing_type_actual_type_id",
    "floorf128",
    "floorf16",
    "floorf32",
    "floorf64",
    "fmaf128",
    "fmaf16",
    "fmaf32",
    "fmaf64",
    "fmul_algebraic",
    "fmuladdf128",
    "fmuladdf16",
    "fmuladdf32",
    "fmuladdf64",
    "forget",
    "frem_algebraic",
    "fsub_algebraic",
    "is_val_statically_known",
    "likely",
    "log10f128",
    "log10f16",
    "log10f32",
    "log10f64",
    "log2f128",
    "log2f16",
    "log2f32",
    "log2f64",
    "logf128",
    "logf16",
    "logf32",
    "logf64",
    "maximum_number_nsz_f128",
    "maximum_number_nsz_f16",
    "maximum_number_nsz_f32",
    "maximum_number_nsz_f64",
    "maximumf128",
    "maximumf16",
    "maximumf32",
    "maximumf64",
    "minimum_number_nsz_f128",
    "minimum_number_nsz_f16",
    "minimum_number_nsz_f32",
    "minimum_number_nsz_f64",
    "minimumf128",
    "minimumf16",
    "minimumf32",
    "minimumf64",
    "mul_with_overflow",
    "needs_drop",
    "offload",
    "offset_of",
    "overflow_checks",
    "powf128",
    "powf16",
    "powf32",
    "powf64",
    "powif128",
    "powif16",
    "powif32",
    "powif64",
    "prefetch_read_data",
    "prefetch_read_instruction",
    "prefetch_write_data",
    "prefetch_write_instruction",
    "ptr_guaranteed_cmp",
    "ptr_mask",
    "ptr_metadata",
    "return_address",
    "rotate_left",
    "rotate_right",
    "round_ties_even_f128",
    "round_ties_even_f16",
    "round_ties_even_f32",
    "round_ties_even_f64",
    "roundf128",
    "roundf16",
    "roundf32",
    "roundf64",
    "rustc_peek",
    "saturating_add",
    "saturating_sub",
    "select_unpredictable",
    "sinf128",
    "sinf16",
    "sinf32",
    "sinf64",
    "size_of",
    "size_of_type_id",
    "sqrtf128",
    "sqrtf16",
    "sqrtf32",
    "sqrtf64",
    "sub_with_overflow",
    "three_way_compare",
    "truncf128",
    "truncf16",
    "truncf32",
    "truncf64",
    "type_id",
    "type_id_eq",
    "type_id_field_representing_type",
    "type_id_fields",
    "type_id_variants",
    "type_id_vtable",
    "type_name",
    "type_of",
    "ub_checks",
    "unlikely",
    "va_copy",
    "variant_count",
    "wrapping_add",
    "wrapping_mul",
    "wrapping_sub",
];

/// Is this the leaf name of an intrinsic that `library/core` declares SAFE?
///
/// Unknown names answer `false` — the fail-closed direction.
pub(crate) fn is_safe_core_intrinsic(leaf: &str) -> bool {
    SAFE_CORE_INTRINSICS.binary_search(&leaf).is_ok()
}

/// Check whether a function call name refers to an inherently unsafe function.
///
/// This is the NAME FALLBACK only. The authoritative signal is
/// `Terminator::Call::is_unsafe_sig` (rustc's own `fn_sig().safety()`, recorded
/// at extraction), which every caller consults FIRST; this predicate exists for
/// synthetic / test MIR and old serialized MIR that predate that field.
pub(crate) fn is_unsafe_fn_call(callee: &str) -> bool {
    // INTRINSICS ARE DECIDED BY THE CALLEE'S ACTUAL SAFETY, NOT BY A MODULE
    // SUBSTRING. The list below used to carry a bare `"intrinsics::"` entry —
    // the SAME defect the T5A note at the bottom records for `"::ffi::"`: a
    // MODULE-path substring standing in for a function identity. `ctpop`,
    // `ctlz`, `cttz`, `bswap`, `bitreverse`, `rotate_left`, `wrapping_*`,
    // `saturating_*`, `likely`/`unlikely` are all declared SAFE in
    // `library/core`, and every call to one was being treated as an unsafe
    // block and charged a `[unsafe] missing SAFETY comment` obligation — a
    // `Formula::Bool(true)` row that can never be discharged and that no SAFETY
    // comment can satisfy (`generate_safety_vcs` never reads one).
    // Measured on the `core::num` leaf slice: 21 of 43 failing obligations,
    // 30 % of the whole histogram
    // (`docs/design/2026-08-20-core-slice-blocker-histogram.md` §2.1 row 1).
    //
    // Deciding on the leaf name against the transcribed safe set makes this
    // fallback AGREE WITH `is_unsafe_sig` BY CONSTRUCTION for the intrinsics
    // module — the two now answer the same question from the same source of
    // truth. A genuinely-unsafe intrinsic (`transmute`, `unchecked_shl`,
    // `ctlz_nonzero`, `copy`, `assume`, `volatile_*`, `atomic_*`, …) is NOT in
    // the safe set and is still charged here, exactly as before; so is any
    // intrinsic this list does not know about, and so is every nested-module
    // path (`intrinsics::simd::*`, `intrinsics::mir::*`) that
    // `core_intrinsics_leaf` declines.
    //
    // Why this cannot silently switch off the separation engine — and note the
    // reason CHANGED on 2026-08-28, when the two halves were split. The second
    // consumer of this predicate, `generate::semantic_guard::
    // has_intrinsic_unsafe_surface`, now gates ONLY the doc lint; the sep engine
    // runs under its own `sep_engine::has_unsafe_patterns` (see the split at
    // `generate::entry`). So this predicate closing cannot reach the sep engine
    // at all any more — the engine's admission does not consult it.
    //
    // The ORIGINAL argument is kept because it is still the reason the doc-lint
    // half is safe to close here: such a function has, by definition, no unsafe
    // surface to document — the gate's other arms (raw-pointer locals/derefs,
    // `CopyNonOverlapping`, `is_unsafe_sig`) are untouched, and any body that
    // also holds a raw pointer or a genuinely unsafe call still opens it. Pinned by
    // `safe_intrinsic_only_body_has_no_unsafe_surface` and
    // `unsafe_intrinsic_body_still_has_unsafe_surface` in `tests.rs`.
    if let Some(leaf) = core_intrinsics_leaf(callee) {
        return !leaf.is_some_and(is_safe_core_intrinsic);
    }

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
        "set_len",               // Vec::set_len / String/etc.
        "new_unchecked",         // NonNull::new_unchecked, NonZero*, …
        "unreachable_unchecked", // core::hint::unreachable_unchecked
        "from_u32_unchecked",    // char::from_u32_unchecked
        "from_bytes_with_nul_unchecked", // CStr
                                 // NOTE: the "intrinsics::" NAMESPACE entry was deleted — see the
                                 // leaf-name decision at the top of this function, which replaces it.
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
