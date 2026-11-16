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

use super::{SafetyClaim, UnsafeBlock, UnsafeCoverage, UnsafeOrigin};

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
                origin: UnsafeOrigin::Call { is_unsafe_sig, is_foreign },
            });
        }

        // Check for raw pointer dereferences in statements. The statement INDEX
        // is the site's identity (with the block id); its span is diagnostics.
        for (idx, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && has_raw_deref(func, rvalue)
            {
                blocks.push(UnsafeBlock {
                    span: span.clone(),
                    safety_comment: None,
                    safety_claim: None,
                    block_id: block.id,
                    origin: UnsafeOrigin::RawDeref { stmt: idx },
                });
            }
        }
    }

    blocks
}

/// Attach safety comments to detected unsafe blocks.
///
/// TEST-ONLY TODAY: the one production caller passes no comments
/// (`check_unsafe(func, &[], …)` in `generate::entry`; vcgen has no source map),
/// so nothing here reaches a production row. It is kept exact anyway, because an
/// attached claim selects the `Some(claim)` arm of [`generate_safety_vcs`].
///
/// ATTACHMENT IS ADJACENCY, NOT DISTANCE (T10, 2026-10-10). A comment is
/// attached to a block only when nothing but other comments lies between them:
///
/// * a comment that ends on the block's own first line, before the block's
///   start column (`unsafe { /* SAFETY: … */ … }` on one line), or
/// * a comment that ends on the line directly above the block, or
/// * a comment that ends on the line directly above an ALREADY-attached
///   comment — so a `// SAFETY:` line followed by any number of `//`
///   continuation lines (each its own entry in `comments`, as a source map
///   reports line comments) reaches the block through its continuations.
///
/// The old rule ("ends at most two lines above the block") had two faults in
/// opposite directions: it attached a `// SAFETY:` comment separated from the
/// block by a line of CODE (fail-open: a claim about another statement), and
/// it missed a `// SAFETY:` line followed by two or more continuation lines.
/// The chain is computed over the SAME file's comments only; a code line, a
/// blank line or a missing line breaks it (fail-closed: no claim attached).
///
/// Among the attached comments that carry a SAFETY marker line, the closest
/// (latest-ending) one wins, with a stable source/text tie-break so a caller
/// cannot change the attached claim by permuting the comment list.
pub(crate) fn attach_safety_comments(
    blocks: &mut [UnsafeBlock],
    comments: &[(SourceSpan, String)],
) {
    if blocks.is_empty() || comments.is_empty() {
        return;
    }
    for block in blocks.iter_mut() {
        let same_file: Vec<&(SourceSpan, String)> =
            comments.iter().filter(|(span, _)| span.file == block.span.file).collect();
        let mut attached = vec![false; same_file.len()];
        // Leading comments on the block's own first line, ending before it.
        let mut top = block.span.line_start;
        for (i, (span, _)) in same_file.iter().enumerate() {
            if span.line_end == block.span.line_start
                && span.col_end <= block.span.col_start
                && span.line_start <= span.line_end
            {
                attached[i] = true;
                top = top.min(span.line_start);
            }
        }
        // Walk upward through comments that each end on the line directly
        // above the topmost line already reached.
        loop {
            let mut next_top = top;
            for (i, (span, _)) in same_file.iter().enumerate() {
                if !attached[i]
                    && span.line_end.checked_add(1) == Some(top)
                    && span.line_start <= span.line_end
                {
                    attached[i] = true;
                    next_top = next_top.min(span.line_start);
                }
            }
            if next_top == top {
                break;
            }
            top = next_top;
        }
        let closest = same_file
            .iter()
            .zip(&attached)
            .filter(|((_, text), is_attached)| **is_attached && comment_has_safety_line(text))
            .map(|(comment, _)| *comment)
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
    if let Some(because_idx) = after_safety
        .as_bytes()
        .windows(" because ".len())
        .position(|w| w.eq_ignore_ascii_case(b" because "))
    {
        let invariant = after_safety[..because_idx].trim().to_string();
        let justification = after_safety[because_idx + 9..].trim().to_string();
        return SafetyClaim { invariant, justification };
    }

    let invariant = after_safety.to_string();

    // Justification is the remaining lines after the SAFETY: line
    let justification_lines = safety_idx.map_or(&[][..], |idx| &lines[idx + 1..]);

    let justification = if justification_lines.is_empty() {
        "no justification provided".to_string()
    } else {
        justification_lines.join(" ")
    };

    SafetyClaim { invariant, justification }
}

/// Peel `&`/`&mut` layers off a type reference to reach the pointee.
fn peel_refs_ref(mut ty: &Ty) -> &Ty {
    loop {
        match ty {
            Ty::Ref { inner, .. } => ty = inner.as_ref(),
            other => return other,
        }
    }
}

fn block_by_id(func: &VerifiableFunction, block_id: BlockId) -> Option<&BasicBlock> {
    func.body
        .blocks
        .get(block_id.0)
        .filter(|b| b.id == block_id)
        .or_else(|| func.body.blocks.iter().find(|b| b.id == block_id))
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
    let Some(mir) = block_by_id(func, block_id) else {
        return false;
    };
    let (key, args) = match &mir.terminator {
        Terminator::Call { args, callee_key, .. }
        | Terminator::TailCall { args, callee_key, .. } => (callee_key.as_ref(), args),
        _ => return false,
    };
    // RULE 1 belt, ROUND 7: KEYED. This is a SUPERSESSION — answering true
    // WITHHOLDS the fail-closed "missing SAFETY comment" stand-in on the
    // strength of the engine's `UncheckedIndexBounds` row — so true is the
    // PERMISSIVE direction and it may not be reachable from a rendering.
    //
    // What it replaces was `callee_is_authenticated_sysroot(callee) &&
    // callee.contains("::get_unchecked")`: a root test plus a fourteen-byte
    // SUBSTRING, both satisfiable on a GENUINE sysroot callee whose TYPE
    // ARGUMENT happens to name a module or type called `get_unchecked`
    // (`core::ptr::read::<mycrate::get_unchecked::T>` carries both). The stand-in
    // on an unrelated `ptr::read` could then be suppressed by the row of
    // whatever the engine recorded for that block.
    //
    // The four tags below are the slice and `str` unchecked-index items, and
    // nothing else can wear them. An ABSENT key fails closed: the lint is kept.
    if !trust_types::CalleeKey::opt_is_one_of(
        key,
        &[
            trust_types::SysrootItem::SliceGetUnchecked,
            trust_types::SysrootItem::SliceGetUncheckedMut,
            trust_types::SysrootItem::StrGetUnchecked,
            trust_types::SysrootItem::StrGetUncheckedMut,
        ],
    ) || args.len() < 2
    {
        return false;
    }
    // Index must be a SCALAR integer (`usize`). A range index (`a..b`) is a
    // struct — NOT `Ty::Int` — and carries a different precondition, so it fails
    // this gate and keeps its fail-closed lint.
    if !matches!(crate::operand_ty_cow(func, &args[1]).as_deref(), Some(Ty::Int { .. })) {
        return false;
    }
    // Receiver (behind any refs) must be a slice/array, so `len` is its element
    // count. Anything else (e.g. `str`) fails closed.
    matches!(
        crate::operand_ty_cow(func, &args[0]).as_deref().map(peel_refs_ref),
        Some(Ty::Slice { .. } | Ty::Array { .. })
    )
}

/// The stand-in row's message. Serialized into SHA-256 receipts and `report.json`
/// for every site that still carries it, so it is BYTE-FROZEN: a site that keeps
/// its stand-in after this change hashes exactly as it did before.
pub(crate) const MISSING_SAFETY_STANDIN_MSG: &str =
    "[unsafe] missing SAFETY comment on unsafe block";

/// Does `callee` name EXACTLY the sysroot item `path` (no generic parameters of
/// its own beyond an instantiation turbofish)? The extractor renders a callee
/// under a sysroot-looking crate that is NOT the real sysroot with the
/// `TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX` stamp (`direct_call_def_path`), so a
/// forged `core::mem::zeroed` never matches and keeps its fail-closed stand-in.
/// `core::mem::zeroed_like` is not matched either: the only admitted
/// continuations after `path` are the end of the string, `::<…>` and `<…>`.
/// ROUND 7: NO LONGER ON ANY DECISION PATH — `blanket_only_op` was its last
/// caller and now matches on the tag. Kept for the same reason as
/// [`callee_is_authenticated_sysroot`].
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "retired from the decision path in round 7; kept as the documented before-half, exercised by its own tests"
    )
)]
pub(crate) fn callee_is_sysroot_item(callee: &str, path: &str) -> bool {
    match callee.strip_prefix(path) {
        Some("") => true,
        Some(rest) => rest.starts_with("::<") || rest.starts_with('<'),
        None => false,
    }
}

/// Is `callee` a SYSROOT-AUTHENTICATED item — the only kind of callee a
/// separation row may COVER (rule 1, `decide_site`)? Leans on the extractor's
/// stamp the way [`callee_is_sysroot_item`] does: a crate impersonating
/// `core`/`alloc`/`std` renders with the `TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX`
/// stamp (`direct_call_def_path`), which a user crate cannot forge, and
/// `trust_types::path_root_is_authenticated_sysroot_crate` rejects it anywhere in
/// the path while requiring the `core::`/`alloc::`/`std::` root.
///
/// Spellings: a plain path (`core::ptr::read::<u8>`,
/// `alloc::vec::Vec::<u8>::set_len`, `core::num::nonzero::NonZero::<u32>::
/// new_unchecked` — real extracted MIR) must be sysroot-rooted at its front. A
/// UFCS path `<Q>::m` is decided on its qualifier `Q`: an inherent header
/// (`<core::…>`, or the primitive raw-pointer header `<*const T>` / `<*mut T>`,
/// to which no user crate can add inherent methods) must be sysroot-rooted; a
/// trait-qualified `<Self as Trait>` must have BOTH halves sysroot-rooted — the
/// genuine `<alloc::alloc::Global as core::alloc::Allocator>::deallocate`
/// (round-two `optbox`, covered by its alloc rows) passes, while a user impl of a
/// sysroot trait (`<optbox::BoolAlloc as core::alloc::Allocator>::deallocate`) and
/// a user trait on a sysroot type (`<core::num::nonzero::NonZero<u32> as
/// mycrate::Forge>::new_unchecked`) both fail closed. Every genuine
/// separation-terminator callee renders in one of the admitted shapes, so this
/// never withholds coverage from a genuine sysroot call; it withholds it only
/// from a NON-sysroot callee some recognizer minted a row for.
/// ROUND 7: NO LONGER ON ANY DECISION PATH. Both of its callers — `decide_site`
/// RULE 1 and the `get_unchecked` supersession belt — now read
/// `CalleeKey::krate_is_real_sysroot` and the `SysrootItem` tags instead, which
/// is the compiler's own artifact-residency verdict rather than a `__trust_crate@`
/// prefix test plus a `>::` scan over a UFCS qualifier. It is KEPT, exercised by
/// its tests, because it is still the precise statement of what the old string
/// lane could and could not authenticate, and because deleting it would erase
/// the before-half of this round's comparison.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "retired from the decision path in round 7; kept as the documented before-half, exercised by its own tests"
    )
)]
pub(crate) fn callee_is_authenticated_sysroot(callee: &str) -> bool {
    use trust_types::path_root_is_authenticated_sysroot_crate as sysroot_rooted;
    if trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return false;
    }
    let Some(inner) = callee.strip_prefix('<') else {
        return sysroot_rooted(callee);
    };
    // The qualifier runs to the `>::` that closes it; a `>` inside a nested
    // generic is followed by `>`, `,` or a space, never by `::` (a projection
    // nested inside the qualifier cuts it short and fails closed).
    let Some(end) = inner.find(">::") else {
        return false;
    };
    let qualifier = inner[..end].trim();
    let inherent_ok = |ty: &str| {
        let ty = ty.trim();
        sysroot_rooted(ty) || ty.starts_with("*const ") || ty.starts_with("*mut ")
    };
    match qualifier.split_once(" as ") {
        Some((self_ty, trait_path)) => inherent_ok(self_ty) && sysroot_rooted(trait_path.trim()),
        None => inherent_ok(qualifier),
    }
}

/// WHY THERE IS NO `compiler_mints_unmodeled_call_row` HERE ANY MORE
/// (2026-09-20, the `Covered` asymmetry).
///
/// Four functions lived at this spot: `strip_unauthenticated_crate_stamp`,
/// `strip_instantiation_args`, and the two arms of the predictor that used
/// them. Together they answered ONE question — "will the compiler mint its
/// fail-closed `[unsafe:unmodeled-call]` row for this call?" — by MIRRORING
/// `crate::call_has_unsafe_model` across a spelling gap: the compiler evaluates
/// it on the bare `safe_def_path_str`, vcgen held the instantiated and possibly
/// identity-stamped rendering, and the mirror tried to stay conservative by
/// requiring all four spellings to agree.
///
/// IT COULD NOT BE MADE SAFE, because the two directions are not symmetric.
/// The branch's own justification for leaving the text in the suppression
/// mirror covers only a spurious TRUE ("it can only decline to refute, and
/// `decide_site` answers a declined refutation with the fail-closed stand-in").
/// A desynchronized scan produces a spurious FALSE:
/// `callee_is_sysroot_spelling_for_suppression` is a BYTE COMPARE after
/// normalization, so extra text in a turbofish can only be LOST past it, never
/// gained. A lost match means "unmodeled" here, which made this predictor
/// answer TRUE, which made [`decide_site`] answer `SiteDecision::Covered` and
/// DELETE the byte-frozen stand-in — while the compiler, reading the bare path,
/// found the callee modeled and minted nothing at all. Net: an unsafe site with
/// ZERO obligations, arrived at by deleting the only row it had.
///
/// (MEASURED, and not exploitable on the sealed compiler: the reviewer's
/// `dropgen`/`dropctl` pair is 7 rows vs 7. What plugged it was an UNDOCUMENTED
/// SECOND BELT — `is_unsafe_fn_call`'s bare substring list, which a mangled
/// turbofish can only GAIN a match in. That belt is what commit D removes, so
/// the hole had to be closed first, and closed by construction rather than by a
/// third scanner.)
///
/// WHAT REPLACES IT: the compiler's OWN ROWS, as
/// `UnsafeCoverage::compiler_unmodeled_call_blocks`. `trust_verify` runs the
/// generator over the same `body` before generation and installs the block set
/// of the rows it produced. `Covered` is now a statement about a row that
/// EXISTS, not a bet on one that might; an absent set is empty and empty keeps
/// every stand-in.
///
/// `strip_instantiation_args` went with them, and this is the disposition the
/// round-6 arrow defect finally gets: it never had the `-` lookbehind that
/// `sep_engine::strip_turbofish_args` grew, so `ptr::read::<fn() -> u8>`
/// normalized to `core::ptr::read u8>` in it to the very end. It had no caller
/// outside this predictor and no caller on any decision path, so it is deleted
/// rather than patched. A scanner that is not consulted cannot be
/// desynchronized.

/// Short, deterministic rendering of a `Ty`'s SHAPE for obligation messages
/// (there is no `Display` for `Ty`). Only the shape and the authenticated ADT
/// name are rendered, never field lists.
fn describe_ty(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".into(),
        Ty::Int { width, signed } => format!("{}{width}", if *signed { "i" } else { "u" }),
        Ty::PtrSizedInt { signed } => if *signed { "isize" } else { "usize" }.into(),
        Ty::Char => "char".into(),
        Ty::Float { width } => format!("f{width}"),
        Ty::Ref { mutable, inner } => {
            format!("&{}{}", if *mutable { "mut " } else { "" }, describe_ty(inner))
        }
        Ty::RawPtr { mutable, pointee } => {
            format!("*{} {}", if *mutable { "mut" } else { "const" }, describe_ty(pointee))
        }
        Ty::Slice { elem } => format!("[{}]", describe_ty(elem)),
        Ty::Seq { elem, .. } => format!("Vec<{}>", describe_ty(elem)),
        Ty::Str => "str".into(),
        Ty::Array { elem, len } => format!("[{}; {len}]", describe_ty(elem)),
        Ty::SymArray { elem, .. } => format!("[{}; N]", describe_ty(elem)),
        Ty::Tuple(elems) => {
            format!("({})", elems.iter().map(describe_ty).collect::<Vec<_>>().join(", "))
        }
        Ty::Adt { name, .. } | Ty::Datatype { name, .. } => name.clone(),
        Ty::Bv(width) => format!("bv{width}"),
        Ty::Unit => "()".into(),
        Ty::Never => "!".into(),
        Ty::Closure { name, .. } | Ty::Coroutine { name, .. } | Ty::FnDef { name, .. } => {
            name.clone()
        }
        Ty::FnPtr { .. } => "fn pointer".into(),
        Ty::Dynamic { trait_name, .. } => format!("dyn {trait_name}"),
        Ty::Unsupported { kind, .. } => format!("<unsupported {kind}>"),
        Ty::BignumNat => "bignum".into(),
        // `Ty` is `#[non_exhaustive]`: a variant this crate does not know yet.
        _ => "<unknown type>".into(),
    }
}

/// Is `pointee` a type whose RAW POINTER is thin, or fat with an integer length
/// (slice/`str`), so that the all-zero raw pointer is a valid value? A raw
/// pointer to `dyn Trait` is fat with a VTABLE pointer, and a null vtable is an
/// invalid value (Reference, "invalid metadata"); a pointer to an ADT may be such
/// a custom DST (the legacy lowering does not say), so only positively-thin
/// pointees and the two integer-metadata DSTs answer `true`.
fn raw_pointer_all_zero_is_valid(pointee: &Ty) -> bool {
    match pointee {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::Slice { .. }
        | Ty::Str
        | Ty::Array { .. }
        | Ty::SymArray { .. }
        | Ty::Unit
        | Ty::Never
        | Ty::FnPtr { .. }
        | Ty::Bv(_) => true,
        Ty::Tuple(elems) => elems.iter().all(raw_pointer_all_zero_is_valid),
        _ => false,
    }
}

/// Does `ty` positively admit the ALL-ZERO bit pattern as a valid value — the
/// obligation `mem::zeroed::<T>()` owes? `Ok(())` = admits; `Err(why)` = refute,
/// with the reason for the obligation message.
///
/// TOTAL and FAIL-CLOSED: every shape this function does not positively
/// recognise is `Err`. The admitted set is deliberately narrow because the legacy
/// `Ty` lowering ERASES pattern-type refinements (`trust-mir-extract`'s
/// `TyKind::Pat(inner, _)` arm lowers to `inner`): a `NonZero<u32>` arrives as a
/// struct with one `u32` field and a `NonNull<T>` as a struct with one `*const T`
/// field, indistinguishable from a plain newtype. No ADT's field list can
/// therefore be trusted to carry the type's validity invariant, so EVERY struct
/// and union is refuted, and enums are admitted only through two rustc-layout
/// facts the lowering does carry:
///
/// * `Option<X>` (sysroot-authenticated name, two variants, `None` with
///   discriminant 0 and no fields, `Some` with exactly one field) where `X` is a
///   reference, a function pointer, or the authenticated `NonNull`/`Box` — the
///   null-pointer-optimisation guarantee that `None` IS the all-zero pattern.
/// * `disc_index_safe` — `true` ONLY when rustc's layout is
///   `Variants::Multiple { tag_encoding: Direct }` — so the all-zero pattern is
///   the variant whose discriminant is 0 with an all-zero payload; admitted iff
///   such a variant exists and each of its fields admits zero by this predicate.
///
/// Primitives: `bool` (0 = `false`), every integer and float, `char` (U+0000),
/// `()`; raw pointers whose pointee is positively thin or an integer-metadata
/// DST (a null `*const dyn Trait` carries an invalid vtable); arrays, symbolic
/// arrays and tuples of admitting element types. References, `Box`, `NonNull`,
/// `NonZero*`, function pointers, `Vec`, `str`, `!`, closures, trait objects and
/// every `Unsupported` lowering refute.
///
/// Note on the pattern-type erasure at a PRIMITIVE position: a bare
/// `pattern_type!(u32 is 1..)` (unstable `pattern_types`) also lowers to `u32`
/// and would be admitted. That is a runtime abort, not undefined behaviour:
/// `mem::zeroed` calls `intrinsics::assert_zero_valid::<T>()` first, whose lax
/// validity check inspects every scalar's valid range through struct, tuple and
/// array fields and panics (`panic_nounwind`) when 0 is excluded. The one class
/// that check does NOT see — multi-variant enum payloads — is exactly the class
/// this predicate refuses to admit structurally.
pub(crate) fn zeroed_all_zero_verdict(ty: &Ty) -> Result<(), String> {
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Unit
        | Ty::Bv(_) => Ok(()),
        Ty::RawPtr { pointee, .. } => {
            if raw_pointer_all_zero_is_valid(pointee) {
                Ok(())
            } else {
                Err(format!(
                    "`{}` may be a wide pointer with a vtable, and a null vtable is invalid metadata",
                    describe_ty(ty)
                ))
            }
        }
        Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => zeroed_all_zero_verdict(elem),
        Ty::Tuple(elems) => elems.iter().try_for_each(zeroed_all_zero_verdict),
        Ty::Ref { .. } => Err(format!("`{}` is a reference; null is never valid", describe_ty(ty))),
        Ty::FnPtr { .. } => Err("a function pointer is never null".to_string()),
        Ty::Adt { name, variants, disc_index_safe, .. } => {
            if variants.is_empty() {
                // Struct or union: the field list cannot carry a pattern-type
                // validity invariant (see the doc comment), so fail closed.
                return Err(format!(
                    "`{name}` is a struct/union; the legacy type lowering erases pattern-type \
                     validity invariants (`NonZero`, `NonNull`, …), so no field list is trusted"
                ));
            }
            if option_niche_all_zero_is_none(name, variants) {
                return Ok(());
            }
            if *disc_index_safe {
                // Direct tag encoding: the all-zero pattern IS the discriminant-0
                // variant with an all-zero payload.
                return match variants.iter().find(|v| v.discriminant == 0) {
                    Some(zero) => zero
                        .fields
                        .iter()
                        .try_for_each(|(_, fty)| zeroed_all_zero_verdict(fty))
                        .map_err(|why| {
                            format!("`{name}::{}`'s payload does not admit zero: {why}", zero.name)
                        }),
                    None => Err(format!("`{name}` has no variant with discriminant 0")),
                };
            }
            Err(format!(
                "`{name}` is a niche-encoded or layout-unknown enum whose all-zero pattern \
                 cannot be identified from its variants"
            ))
        }
        Ty::Slice { .. }
        | Ty::Seq { .. }
        | Ty::Str
        | Ty::Datatype { .. }
        | Ty::Never
        | Ty::Closure { .. }
        | Ty::FnDef { .. }
        | Ty::Dynamic { .. }
        | Ty::Coroutine { .. }
        | Ty::Unsupported { .. }
        | Ty::BignumNat => Err(format!(
            "`{}` is not a type this predicate recognises as zero-valid",
            describe_ty(ty)
        )),
        // `Ty` is `#[non_exhaustive]`: an unknown variant is refuted.
        _ => Err("an unrecognised type variant is not known to admit the all-zero pattern".into()),
    }
}

/// The null-pointer-optimisation guarantee: `Option<&T>`, `Option<&mut T>`,
/// `Option<fn(..)>`, `Option<NonNull<T>>` and `Option<Box<T>>` are documented to
/// have the pointer's size with `None` represented by the null pointer, i.e. the
/// all-zero pattern IS `None`. The outer and inner ADT names are the extractor's
/// SYSROOT-AUTHENTICATED spellings (`sysroot_authenticated_def_path_str`, which
/// stamps an impersonating crate), rendered without generic arguments.
///
/// THE ALLOCATOR PARAMETER. The guarantee is for `Box<T>` = `Box<T, Global>`.
/// `Box<T, A>` is `struct Box<T, A>(Unique<T>, A)`, and rustc places
/// `Option`'s niche in whichever field offers the LARGEST one: with an
/// `allocator_api` allocator carrying a `bool` or a small enum (254 / 253 spare
/// values against `NonNull`'s one) the niche moves into `A`, and the all-zero
/// pattern is `Some(Box { ptr: null, alloc: 0 })` — undefined behaviour
/// (REFUTED 2026-09-19, `optbox.rs`: `zeroed::<Option<Box<u8, BoolAlloc>>>()
/// .is_some()` prints `true` and the deref traps). The args-erased name
/// `alloc::boxed::Box` cannot see `A`, but the extractor lowers every field with
/// the call's concrete arguments substituted (`f.ty(tcx, args)`), so the
/// allocator IS the Box's second field: `Box<T, A>` is admitted only when that
/// field is the authenticated unit struct `alloc::alloc::Global`
/// ([`box_allocator_is_global`]). A Box whose extracted field list does not
/// show that — one field, no fields, a compacted `Ty::Datatype` marker, a
/// pre-P4 fixture — is REFUTED: a false refutation of `Option<Box<T>>` is the
/// price, never a false proof. `NonNull<T>` has a single generic parameter and
/// no field that could carry a competing niche; `&T` and `fn` have none.
fn option_niche_all_zero_is_none(name: &str, variants: &[VariantDef]) -> bool {
    if name != "core::option::Option" || variants.len() != 2 {
        return false;
    }
    let Some(none) = variants.iter().find(|v| v.name == "None") else { return false };
    let Some(some) = variants.iter().find(|v| v.name == "Some") else { return false };
    if none.discriminant != 0 || !none.fields.is_empty() || some.fields.len() != 1 {
        return false;
    }
    match &some.fields[0].1 {
        Ty::Ref { .. } | Ty::FnPtr { .. } => true,
        Ty::Adt { name, fields, .. } => {
            name == "core::ptr::non_null::NonNull"
                || (name == "alloc::boxed::Box" && box_allocator_is_global(fields))
        }
        _ => false,
    }
}

/// Is this extracted `alloc::boxed::Box` field list `(Unique<T>, Global)` —
/// i.e. is the allocator parameter positively the default `alloc::alloc::Global`
/// (a fieldless unit struct, sysroot-authenticated spelling)? Exactly two
/// fields, second one `Global`; anything else answers `false`.
fn box_allocator_is_global(fields: &[(String, Ty)]) -> bool {
    match fields {
        [_, (_, Ty::Adt { name, fields, variants, .. })] => {
            name == "alloc::alloc::Global" && fields.is_empty() && variants.is_empty()
        }
        _ => false,
    }
}

/// Is `ty` positively a ZERO-SIZED type — the only `T` for which
/// `mem::uninitialized::<T>()` is not undefined behaviour? `Ok(())` = ZST;
/// `Err(why)` = refute. TOTAL and FAIL-CLOSED: `()`, tuples and arrays of ZSTs, a
/// zero-length array of anything, and a `struct` (extractor-stamped
/// `AdtKind::Struct`, no variants) all of whose fields are ZSTs. A struct's
/// field list is trusted HERE because zero-sizedness is a layout property the
/// field types carry faithfully (a pattern-typed field is still non-zero-sized;
/// a `Ty::Unsupported` field refutes). Everything else — every integer, pointer,
/// enum, union, `!`, closure, fn item — refutes.
pub(crate) fn uninitialized_zst_verdict(ty: &Ty) -> Result<(), String> {
    match ty {
        Ty::Unit => Ok(()),
        Ty::Array { len: 0, .. } => Ok(()),
        Ty::Array { elem, .. } => uninitialized_zst_verdict(elem),
        Ty::Tuple(elems) => elems.iter().try_for_each(uninitialized_zst_verdict),
        Ty::Adt { name, fields, variants, adt_kind: Some(AdtKind::Struct), .. }
            if variants.is_empty() =>
        {
            fields
                .iter()
                .try_for_each(|(_, fty)| uninitialized_zst_verdict(fty))
                .map_err(|why| format!("`{name}` has a non-zero-sized field: {why}"))
        }
        _ => Err(format!("`{}` is not a zero-sized type", describe_ty(ty))),
    }
}

/// The three unsafe operations for which the stand-in row was MEASURED to be the
/// SOLE unsafe obligation (see `generate_safety_vcs`) and which now mint the
/// obligation they actually owe.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BlanketOnlyOp {
    /// `core::mem::zeroed::<T>()` — UB iff `T` does not admit the all-zero pattern.
    Zeroed,
    /// `core::mem::uninitialized::<T>()` — UB for every non-zero-sized `T`.
    Uninitialized,
    /// `core::hint::unreachable_unchecked()` — UB iff reachable.
    UnreachableUnchecked,
}

/// ROUND 7: keyed, because every arm this selects MINTS a typed refutation.
///
/// The three arms decide UB on the DESTINATION TYPE (`zeroed`/`uninitialized`)
/// or on reachability (`unreachable_unchecked`), and charging one of them to the
/// wrong callee states the wrong contract for the site — the same class as the
/// `NonZero` niche minted for `dep::nonzero::Handle::new_unchecked` (REFUTED
/// 2026-09-19). The string tests this replaces were
/// `callee_is_sysroot_item(callee, "core::mem::zeroed")` — an instantiation
/// strip plus a stamp strip plus a byte compare — and
/// `terminator_obligations::is_unreachable_unchecked_call`, a shared string
/// recognizer. Both are readings of a rendering; the tags are not.
///
/// `None` (no key, or a key with no tag) selects NO arm, which leaves the site
/// its fail-closed stand-in.
pub(crate) fn blanket_only_op(key: Option<&trust_types::CalleeKey>) -> Option<BlanketOnlyOp> {
    match key?.sysroot_item? {
        trust_types::SysrootItem::MemZeroed => Some(BlanketOnlyOp::Zeroed),
        trust_types::SysrootItem::MemUninitialized => Some(BlanketOnlyOp::Uninitialized),
        trust_types::SysrootItem::HintUnreachableUnchecked => {
            Some(BlanketOnlyOp::UnreachableUnchecked)
        }
        _ => None,
    }
}

/// The message prefix of the typed row minted for a raw-pointer reborrow
/// (`&*p`, `&mut *p`, `&(*p).f`): see [`raw_reborrow_message`].
pub(crate) const RAW_REBORROW_MSG_PREFIX: &str = "[unsafe:reborrow]";

/// The typed row for a raw-pointer reborrow the separation engine did not
/// interpret. It names the obligation actually owed — the produced reference
/// must be non-null, aligned, dereferenceable, point at a valid initialized
/// value, and respect the aliasing rules for its whole lifetime — and says
/// plainly that Trust has no model of it. Deterministic in `mutable` only.
pub(crate) fn raw_reborrow_message(mutable: bool) -> String {
    let (spelling, alias) = if mutable {
        ("&mut *ptr", "unaliased")
    } else {
        ("&*ptr", "not mutated through another pointer")
    };
    format!(
        "{RAW_REBORROW_MSG_PREFIX} `{spelling}` reborrows a raw pointer into a reference; \
         Trust has no model of the reference's validity (non-null, aligned, dereferenceable, \
         initialized, {alias} for its whole lifetime), so the site is unproved (fail-closed; \
         a `// SAFETY:` comment documents it but does not discharge it)"
    )
}

/// `Some(mutable)` iff statement `stmt` of block `block_id` is
/// `_d = &[mut] <place>` whose place goes THROUGH a raw-pointer deref — the
/// reborrow the separation engine never interprets. Keyed on the statement's
/// own rvalue (never a span); any other shape (a read, a `CopyForDeref`, a
/// missing block or statement) answers `None` and keeps the stand-in.
fn raw_reborrow_mutability(
    func: &VerifiableFunction,
    block_id: BlockId,
    stmt: usize,
) -> Option<bool> {
    let mir = block_by_id(func, block_id)?;
    match mir.stmts.get(stmt)? {
        Statement::Assign { rvalue: Rvalue::Ref { mutable, place }, .. }
            if crate::place_has_raw_deref(func, place) =>
        {
            Some(*mutable)
        }
        _ => None,
    }
}

/// What the mint decides for one detected site once the scoping skips have
/// passed: keep the byte-frozen stand-in, mint a NEW typed refutation, mint
/// nothing because a real obligation already covers the site, or mint nothing
/// because the site is DECLARED by a clippy-placed `// SAFETY:` comment and the
/// compiler charges its block an `assumption:safety-comment` row
/// (SAFETY-ASSUME-1; see [`declared_or`]).
enum SiteDecision {
    StandIn,
    Refute(String),
    Covered,
    Declared,
}

/// SAFETY-ASSUME-1 (ruled 2026-10-17): `decision`, unless the compiler declared
/// this site — an operation inside a user `unsafe { }` block whose `// SAFETY:`
/// comment sits where `clippy::undocumented_unsafe_blocks` accepts one — in which
/// case [`SiteDecision::Declared`]. The scope RECORDS the site before answering,
/// and the compiler charges the block for every recorded site, so the row this
/// replaces never vanishes without its assumption row.
///
/// Applied ONLY where the answer would otherwise be one of the two "Trust has no
/// model of this" rows: the byte-frozen stand-in on the foreign-call and
/// unsafe-signature fallbacks, and the T10 `[unsafe:reborrow]` row. Never on the
/// raw-deref fallback: a raw READ the engine did not interpret is an engine gap,
/// since the engine models raw reads with `[unsafe:sep:deref]`. Never before a
/// `Covered` arm (a real obligation stays), never on the typed
/// `[unsafe:zeroed]` / `[unsafe:uninitialized]` refutations (Trust decides those
/// on the type), never on the unreached `unreachable_unchecked` stand-in, and
/// never on a call to an operation Trust MODELS whose row the engine did not mint
/// (a vocabulary item, a foreign memory-map callee, an unchecked index): that
/// stand-in is an engine gap, kept FAILED (`modeled_operation` in
/// [`decide_site`]). A Rust wrapper's map call (`memmap2::…`) is unmodeled on the
/// compiler side, so its `[unsafe:unmodeled-call]` row is withheld like any other.
fn declared_or(
    func: &VerifiableFunction,
    block: &UnsafeBlock,
    decision: SiteDecision,
) -> SiteDecision {
    if super::safety_declared::withhold_declared_site(func, block) {
        SiteDecision::Declared
    } else {
        decision
    }
}

/// Decide a detected site. Every arm's justification is written next to it; the
/// rule is that the guard's scope must never exceed its justification's scope,
/// and every unrecognised shape lands on `StandIn`.
fn decide_site(
    func: &VerifiableFunction,
    block: &UnsafeBlock,
    coverage: &UnsafeCoverage,
) -> SiteDecision {
    match block.origin {
        // A raw-pointer DEREFERENCE statement. The separation engine mints the
        // `[unsafe:sep:deref]` null / allocation-validity / alignment rows for
        // every raw deref it interprets (`interpret_raw_deref_read`/`_write`).
        // Those rows ARE the UB conditions of the deref; the stand-in asserts
        // nothing beyond them. Coverage is keyed on the OPERATION — this block,
        // this statement index — so only a deref-family row the engine minted
        // while interpreting THIS statement counts: a `ptr::read`/`ptr::write`
        // CALL in the same block mints the same family but is charged to the
        // terminator, and under a proc-macro `call_site()` span it shares this
        // statement's span, which is why the span is not the key. A deref the
        // engine did not reach — a body `has_unsafe_patterns` declined, an
        // engine budget — keeps its stand-in, in a SAFETY-declared block too; an
        // `Rvalue::Ref` over a raw deref (never reached) mints the typed
        // `[unsafe:reborrow]` row below.
        UnsafeOrigin::RawDeref { stmt } => {
            if coverage.sep_deref_sites.contains(&(block.block_id, stmt)) {
                return SiteDecision::Covered;
            }
            // T10 (2026-10-10): a REBORROW of a raw pointer — `&*p`, `&mut *p`,
            // `&(*p).field` — is an operation the separation engine does not
            // interpret, so nothing else covers it. It used to keep the
            // byte-frozen stand-in, whose text ("missing SAFETY comment") is
            // FALSE for it: no SAFETY comment is ever looked up in production
            // (`check_unsafe(func, &[], …)`), and the row fired byte-identically
            // on `tla-shapes-families` `cvw.rs:532/540`, each of which carries a
            // two-line `// SAFETY:` comment directly above it. The row now says
            // what is actually owed and unproved. SAME constant `Bool(true)`
            // formula, SAME `[unsafe` family, so `refute_unsafe_demand_findings`
            // still forces it `failed` (`unproved_fail_closed`): the verdict,
            // every gate count and every exit code are unchanged — only the
            // message (and so the row's claim digest) moves. A SAFETY comment
            // still discharges nothing (docs/DECISION_QUEUE.md, T10-REBORROW); since
            // SAFETY-ASSUME-1 a clippy-placed one DECLARES the site instead — the
            // row becomes its block's `assumption:safety-comment` charge, never a
            // proof (`declared_or`).
            if let Some(mutable) = raw_reborrow_mutability(func, block.block_id, stmt) {
                return declared_or(
                    func,
                    block,
                    SiteDecision::Refute(raw_reborrow_message(mutable)),
                );
            }
            // SAFETY-ASSUME-1: what is left is a raw-pointer READ (`Use` or
            // `CopyForDeref` through `*p`, `has_raw_deref`'s other two shapes), and
            // Trust MODELS that: the engine mints `[unsafe:sep:deref]` for every one
            // it interprets. It did not interpret this one — a body it declined, a
            // budget — which is an ENGINE gap, not an operation Trust has no model
            // of, so a `// SAFETY:` comment does not declare it: the FAILED stand-in
            // stays, unrecorded, and its block is charged nothing for it. Only the
            // reborrow above, which the engine never interprets, is declared.
            SiteDecision::StandIn
        }
        UnsafeOrigin::Call { is_unsafe_sig, is_foreign } => {
            let Some(mir) = block_by_id(func, block.block_id) else {
                return SiteDecision::StandIn;
            };
            // The KEY comes off the terminator beside the name (round 7). `callee`
            // stays for the ONE remaining STRING consumer below, which mints
            // nothing: `is_external_map_call` (the mmap family, whose legitimate
            // targets are third-party by design — see the residual note). The
            // other one, the compiler-row PREDICTOR, is gone: the compiler's own
            // rows arrive as `coverage.compiler_unmodeled_call_blocks`.
            let (callee, key, dest) = match &mir.terminator {
                Terminator::Call { func, dest, callee_key, .. } => {
                    (func.as_str(), callee_key.as_ref(), Some(dest))
                }
                Terminator::TailCall { func, callee_key, .. } => {
                    (func.as_str(), callee_key.as_ref(), None)
                }
                _ => return SiteDecision::StandIn,
            };
            // (a) The separation engine minted a behavioural `[unsafe:sep:*]` row
            // while interpreting THIS block's TERMINATOR — the call itself: that
            // row states the call's UB condition (`from_raw_parts` bounds,
            // `ptr::read` deref validity, `set_len` capacity, `new_unchecked`
            // non-zero, …). A row the engine minted for a STATEMENT of this block
            // is not in `sep_call_sites`, whatever span it carries, so a deref
            // statement's rows can no longer speak for a `mem::zeroed`, `ptr::swap`
            // or foreign call that shares their proc-macro `call_site()` span.
            //
            // RULE 1 (2026-09-20) — COVERAGE MAY TRUST A SEPARATION ROW ONLY WHEN
            // THE CALLEE IS THE ITEM THE RECOGNIZER MEANT. A `[unsafe:sep:*]` row
            // covers this call only if the callee is SYSROOT-AUTHENTICATED
            // (its `CalleeKey` names one of the DECLARED sysroot items). A call
            // to any other callee keeps the stand-in no matter what rows the
            // engine minted for it. The recognizers themselves are now exact
            // sysroot spellings (`sep_engine`), so a row on a non-sysroot callee
            // should no longer exist; this gate is the belt for any recognizer
            // that is, or is ever again, left name-based — the way the bare
            // `is_nonzero_new_unchecked_call` minted the `NonZero` contract for a
            // user's `dep::nonzero::Handle::new_unchecked` (REFUTED 2026-09-19).
            // The ONE exception is the external-memory-map recognizer, whose
            // legitimate targets are THIRD-PARTY (`libc::mmap`, `memmap2::…`) and
            // therefore never sysroot: its `[unsafe:sep:map]` row is trusted for
            // its own callee, re-checked here (`is_external_map_call`).
            //
            // ROUND 7: the sysroot half of this gate is now the COMPILER's own
            // identity verdict, not a reading of the rendered path.
            // `is_real_sysroot_crate(tcx, def_id.krate)` — artifact residency in
            // the compiler's own target lib dir — is carried verbatim across the
            // artifact boundary. The string predicate it replaced had to
            // re-derive that from a `__trust_crate@` prefix that ALSO means
            // "duplicate crate name", plus a `>::`-scan over a UFCS qualifier:
            // two readings of attacker-influenced text to recover one bit the
            // compiler already knew. An ABSENT key fails closed (no coverage,
            // stand-in kept).
            //
            // THE ITEM, NOT THE CRATE (2026-09-20). This asked
            // `key.krate_is_real_sysroot` — a CRATE-level fact — while the
            // ITEM-level `sysroot_item` sits in the same struct. The gate exists
            // to answer "is this callee the item the recognizer MEANT?", and the
            // crate-level bit answers a weaker question: it admits EVERY item of
            // every genuine sysroot crate, so an `[unsafe:sep:*]` row minted for
            // a sysroot callee the recognizer did not mean — the exact failure
            // the gate is the belt against, only inside the sysroot instead of
            // outside it — still deleted that site's stand-in. `sysroot_item` is
            // `Some` for precisely the declared vocabulary
            // (`trust_types::callee_key::DECLS`), which is precisely the set the
            // minting recognizers can name, so a row on anything else now keeps
            // its stand-in.
            // A refusal-only tag (std thread spawn) is not part of the declared
            // vocabulary the minting recognizers name: `modeled_sysroot_item`.
            let is_external_map = || {
                if !contains_ascii_case_insensitive(callee, "mmap")
                    && !contains_ascii_case_insensitive(callee, "memmap")
                {
                    return false;
                }
                let lower: std::borrow::Cow<'_, str> =
                    if callee.bytes().any(|b| b.is_ascii_uppercase()) {
                        callee.to_ascii_lowercase().into()
                    } else {
                        callee.into()
                    };
                crate::sep_engine::is_external_map_call(&lower)
            };
            let sysroot_authenticated = key.is_some_and(|k| k.modeled_sysroot_item().is_some());
            if coverage.sep_call_sites.contains(&block.block_id)
                && (sysroot_authenticated || is_external_map())
            {
                return SiteDecision::Covered;
            }
            // SAFETY-ASSUME-1: A MODELED OPERATION KEEPS ITS STAND-IN. From here on
            // no row the engine minted covers this call. When the callee is one
            // Trust MODELS — an item of the declared vocabulary, a FOREIGN
            // memory-map callee (an `extern`-block `mmap`/`mmap64`, `libc`'s
            // included), and the scalar `get_unchecked` whose
            // `UncheckedIndexBounds` row the mint loop did not find for this
            // terminator (`block_is_bounds_complete_unchecked_index`; its four
            // tags are vocabulary items, so this names that case rather than
            // widening the set) — the missing row is an ENGINE gap: a body the
            // engine declined, a budget, a shape its recognizer did not match. It
            // is not an operation Trust has no model of, which is all a
            // `// SAFETY:` comment may declare. So the site keeps its FAILED
            // stand-in and the gap stays visible: it is never withheld and never
            // recorded, and its block is charged nothing for it. A vocabulary
            // item whose engine arm mints no row at all
            // (`Layout::from_size_align_unchecked`, the two `drop_in_place`s)
            // therefore keeps its stand-in for good, declared or not: fail-closed,
            // and a capability cost (docs/DECISION_QUEUE.md SAFETY-ASSUME-1).
            //
            // A RUST WRAPPER'S MAP CALL (`memmap2::MmapMut::map_mut`) IS NOT
            // MODELED HERE, although the arm above trusts its `[unsafe:sep:map]`
            // row. The compiler does not model it: `call_has_unsafe_model_keyed`
            // is false for a callee outside the sysroot, so the compiler mints
            // `[unsafe:unmodeled-call]` for it, WITHHOLDS that row in a declared
            // block (`safety_comment_assumption`) and charges the block itself,
            // and the compiler-evidence arm below answers `Covered` before any
            // stand-in. Counting it modeled would only name a stand-in that
            // production never reaches. Its `[unsafe:sep:map]` row stays when the
            // engine minted it (the `Covered` arm above); outside the compiler
            // (no evidence) it is declared like any other unmodeled call.
            let stand_in = || {
                let modeled_operation = sysroot_authenticated
                    || (is_foreign && is_external_map())
                    || block_is_bounds_complete_unchecked_index(func, block.block_id);
                if modeled_operation {
                    SiteDecision::StandIn
                } else {
                    declared_or(func, block, SiteDecision::StandIn)
                }
            };
            // A foreign item is covered by the FFI lane, which mints per summary
            // and CAN mint nothing for a summarised call — a trust surface this
            // change does not audit. Keep the stand-in (unless a SAFETY comment
            // declares the site, SAFETY-ASSUME-1; the FFI lane's rows stay). A
            // foreign `mmap` the map recognizer names is a modeled operation, and
            // keeps the stand-in when the engine minted no `[unsafe:sep:map]` row.
            if is_foreign {
                return stand_in();
            }
            // (a) THE COMPILER ALREADY MINTED `[unsafe:unmodeled-call]` FOR THIS
            // CALL — the fail-closed "no model" obligation, which already
            // refutes it, so a stand-in beside it asserts nothing new.
            //
            // POSITIVE EVIDENCE, NOT A PREDICTION (2026-09-20). This used to ask
            // a vcgen-side mirror of the compiler's string predicate whether the
            // row WOULD be minted, and a mirror that disagrees in the
            // "unmodeled here, modeled there" direction deletes the stand-in and
            // receives nothing for it — an unsafe site with zero obligations.
            // See the disposition note above `strip_turbofish_args`' late
            // sibling, at the top of this file. The set below is the compiler's
            // own row set over THIS body, installed before generation ran; an
            // empty set (every caller that is not the compiler) keeps the
            // stand-in, which is the fail-closed answer to "I cannot see the
            // other obligation from here".
            //
            // SAFETY-ASSUME-1: the set is the blocks the COMPILER ACCOUNTED FOR. A
            // call in a SAFETY-declared block whose row the compiler withheld stays
            // in it, because the compiler charges that block its
            // `assumption:safety-comment` row itself (it records its own
            // withholding; it never relies on this mint recording it).
            if coverage.compiler_unmodeled_call_blocks.contains(&block.block_id) {
                return SiteDecision::Covered;
            }
            // Only an unsafe-signature call reaches the typed (b) arms: the name
            // fallback alone (`is_unsafe_fn_call` on a safe-signature call, or
            // fixture MIR predating the flag) says nothing about the callee's
            // identity that the authenticated path check below can rely on.
            let op = if is_unsafe_sig { blanket_only_op(key) } else { None };
            match op {
                // (b) `mem::zeroed::<T>()`: the obligation is "T admits the
                // all-zero bit pattern", decided at the mint on the destination
                // local's extracted type — `T` exactly, since the call's `dest`
                // has the callee's return type before any coercion.
                Some(BlanketOnlyOp::Zeroed) => {
                    let Some(ty) = dest.and_then(|d| crate::place_ty_cow(func, d)) else {
                        return SiteDecision::Refute(
                            "[unsafe:zeroed] `mem::zeroed::<T>()`: the destination type could \
                             not be resolved, so `T` is not known to admit the all-zero bit \
                             pattern (fail-closed)"
                                .to_string(),
                        );
                    };
                    // Trust (G1, 2026-10-27): the structural verdict refutes every
                    // struct and union because the extracted `Ty` erases niches. The
                    // compiler decided THIS call's `T` on its real layout with rustc's
                    // exact validity check (all-zero bytes validated by the
                    // interpreter: scalar ranges, tags, reference/fn/NonNull/NonZero/
                    // pattern-type niches, through every field, element and variant);
                    // its positive verdict for this block covers the site. Positive
                    // evidence only: an empty set (every non-compiler caller) refutes
                    // exactly as before.
                    if coverage.compiler_zero_valid_zeroed_blocks.contains(&block.block_id) {
                        return SiteDecision::Covered;
                    }
                    match zeroed_all_zero_verdict(&ty) {
                        Ok(()) => SiteDecision::Covered,
                        Err(why) => SiteDecision::Refute(format!(
                            "[unsafe:zeroed] `mem::zeroed::<{}>()` is undefined behaviour or a \
                             guaranteed abort: {why}",
                            describe_ty(&ty)
                        )),
                    }
                }
                // (b) `mem::uninitialized::<T>()`: UB for every T but a ZST.
                Some(BlanketOnlyOp::Uninitialized) => {
                    let Some(ty) = dest.and_then(|d| crate::place_ty_cow(func, d)) else {
                        return SiteDecision::Refute(
                            "[unsafe:uninitialized] `mem::uninitialized::<T>()`: the \
                             destination type could not be resolved, so `T` is not known to \
                             be zero-sized (fail-closed)"
                                .to_string(),
                        );
                    };
                    match uninitialized_zst_verdict(&ty) {
                        Ok(()) => SiteDecision::Covered,
                        Err(why) => SiteDecision::Refute(format!(
                            "[unsafe:uninitialized] `mem::uninitialized::<{}>()` is undefined \
                             behaviour for every non-zero-sized type: {why}",
                            describe_ty(&ty)
                        )),
                    }
                }
                // (b) `hint::unreachable_unchecked()`: UB iff reachable. The
                // shared classifier (`terminator_obligations::
                // unreachable_terminator_span`) now names this call, so
                // `generate::safety` arm 1b mints a `VcKind::Unreachable` row for
                // it — over the block's real path guards, proved iff the path
                // condition is unsatisfiable — for every block the path-guard walk
                // reached. Both halves of that minting condition are re-checked
                // here, on this block's own id; a block the walk did not reach
                // (dead, or budget-collapsed) has no such row and keeps its
                // stand-in.
                Some(BlanketOnlyOp::UnreachableUnchecked) => {
                    let minted = coverage.reached_blocks.contains(&block.block_id)
                        && trust_types::terminator_obligations::unreachable_terminator_span(
                            func, mir,
                        )
                        .is_some();
                    if minted { SiteDecision::Covered } else { SiteDecision::StandIn }
                }
                // Every other blanket-only call — `ptr::swap`, `ptr::replace`,
                // `ptr::drop_in_place`, an unsafe `::ffi::` or `::intrinsics::`
                // item, a provenance-only modeled arm such as
                // `Layout::from_size_align_unchecked`, the compiler-generated
                // `fmt::Arguments`/`from_raw_fd`/native-TLS coverage entries, or a
                // safe-signature call caught by the name fallback — has no other
                // obligation and keeps the fail-closed stand-in, byte-identical.
                // A SAFETY comment declares it (SAFETY-ASSUME-1) only when Trust
                // does not model the callee: a vocabulary item such as
                // `ptr::drop_in_place` or `Layout::from_size_align_unchecked`
                // (always: their engine arms mint no row), and a `get_unchecked`
                // the engine minted no row for, keep the stand-in in a declared
                // block too (`modeled_operation`).
                None => stand_in(),
            }
        }
    }
}

/// Generate the per-unsafe-block obligations.
///
/// NOT a documentation lint, although the stand-in row it still mints keeps that
/// historical message. MEASURED (stage2 b1254a567, same crate with and without
/// `// SAFETY:` on each block: byte-identical obligation set): the ONLY
/// production caller is `check_unsafe(func, &[], …)` in `generate::entry` —
/// vcgen has no source-map access, so `comments` is ALWAYS empty,
/// `safety_claim` is ALWAYS `None`, and the `_` arm fires for EVERY detected
/// block. The `Some(claim)` arm is reachable only from unit tests, which attach
/// comments themselves.
///
/// WHAT THE `_` ARM IS. Each detected [`UnsafeBlock`] is one unsafe OPERATION
/// (a call terminator or a raw-deref statement, see [`UnsafeOrigin`]). For most
/// of them a REAL obligation is minted elsewhere — the separation engine's
/// `[unsafe:sep:*]` rows, the compiler's `[unsafe:unmodeled-call]` /
/// `[unsafe:union-field]` / `[unsafe:mutable-static]` rows — and the
/// always-`Bool(true)` stand-in this arm used to add unconditionally asserted
/// nothing those rows do not. MEASURED on the sealed compiler (2026-09-19,
/// `$TMPDIR/mint-probe`): for `mem::zeroed`, `mem::uninitialized` and
/// `hint::unreachable_unchecked` — whose `[unsafe:unmodeled-call]` row
/// `call_has_unsafe_model` suppresses and for which the separation engine has no
/// arm — the stand-in was the SOLE unsafe obligation, and likewise for
/// `ptr::swap`, `ptr::replace`, `ptr::drop_in_place`, unsafe `::ffi::` and
/// `::intrinsics::` items, `Layout::from_size_align_unchecked`, foreign calls
/// and `&*raw` reborrows (`Rvalue::Ref`, which the engine does not interpret;
/// these now mint the typed `[unsafe:reborrow]` row, rule (b') below).
///
/// THE MINT-SIDE RULE, decided per site by [`decide_site`]:
///
/// * (a) a site that already carries a behavioural unsafe row — a separation
///   row the engine minted for this very MIR operation (block + statement
///   index / terminator, never a span), or a `FnDef` call the compiler will
///   mint `[unsafe:unmodeled-call]` for — mints no stand-in;
/// * (b) the three blanket-only operations mint the obligation each owes:
///   `zeroed` and `uninitialized` are decided at the mint on the destination
///   type ([`zeroed_all_zero_verdict`], [`uninitialized_zst_verdict`]) and
///   refute with a typed `[unsafe:zeroed]` / `[unsafe:uninitialized]` row —
///   `Formula::Bool(true)`, force-refuted downstream like every constant
///   `[unsafe` row — unless the type is positively admitted;
///   `unreachable_unchecked` is covered by the `VcKind::Unreachable` row the
///   shared classifier now mints for it;
/// * (b') a raw-pointer REBORROW (`&*p`, `&mut *p`, `&(*p).f`; the engine does
///   not interpret `Rvalue::Ref`) mints a typed `[unsafe:reborrow]` row
///   ([`raw_reborrow_message`]) — same `Bool(true)`, same forced `failed` —
///   instead of the stand-in, whose "missing SAFETY comment" text was false
///   for a commented site (T10, `tla-shapes-families` `cvw.rs:532/540`);
/// * (c) a source `unsafe { }` around safe code is never detected at all
///   (detection is per operation), so it owes nothing — unchanged;
/// * everything else keeps the byte-frozen stand-in (`MISSING_SAFETY_STANDIN_MSG`).
///
/// Convention: `Assertion`s whose message starts `[unsafe` are the unsafe
/// family. `VcKind::hardened_category` maps them to `UnsafeOperation`, and
/// `refute_unsafe_demand_findings` (rustc_mir_transform/trust_verify.rs) forces
/// every constant-formula one of them `Failed` — which is what keeps
/// `VcKind::Assertion`'s blanket `has_runtime_fallback == true` from ever
/// reaching `classify_runtime_disposition` for these rows, and what makes the
/// new typed refutations land as `Failed`, never `Unknown`.
pub(crate) fn generate_safety_vcs(
    func: &VerifiableFunction,
    blocks: &[UnsafeBlock],
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
    coverage: &UnsafeCoverage,
) -> Vec<VerificationCondition> {
    if blocks.is_empty() {
        return Vec::new();
    }
    let mut vcs = Vec::new();
    let mut fn_sym: Option<trust_types::Symbol> = None;

    for block in blocks {
        // SOURCE-LEVEL SCOPING: the stand-in row verifies no behavioral
        // property; the block's own operation is what it stands in for. After
        // inlining, a callee's unsafe block (e.g. std's
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
        // blanket-only class, for which the row dropped here is the SOLE
        // obligation — see this function's doc comment. A cross-file
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
            static TLS_DISCHARGE_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if *TLS_DISCHARGE_DEBUG
                .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_TLS_DISCHARGE_DEBUG"))
            {
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
        // RUSTC'S OWN `.await` LOWERING (AW-1, 2026-10-03). `make_lowered_await`
        // wraps `Future::poll(Pin::new_unchecked(&mut __awaitee),
        // get_context(_task_context))` in an `UnsafeSource::CompilerGenerated`
        // block — invisible to `#![forbid(unsafe_code)]`, unannotatable by the
        // user — and both callees are `unsafe fn`, so this per-operation detector
        // charged every `.await` a stand-in row. The COMPILER names the exact
        // blocks (span marked `DesugaringKind::Await` AND callee the
        // `PinNewUnchecked`/`GetContext` lang item); vcgen cannot, because
        // `SourceSpan` drops the `SyntaxContext`. Keyed on the block's own CALL
        // TERMINATOR: a raw deref statement in the same block is a different
        // operation and keeps its row, and a user `unsafe { … }` call anywhere in
        // an async body — the awaited operand included — is a different block
        // and keeps its row. Proc-macro expansions are untouched (D29). TCB:
        // docs/TCB.md, "rustc's own `.await` lowering".
        if matches!(block.origin, UnsafeOrigin::Call { .. })
            && coverage.await_desugared_unsafe_call_blocks.contains(&block.block_id)
        {
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
                //
                // The two prose-triggered follow-up rows this arm used to add (a
                // `claim_ptr == 0` "null pointer check" on the substrings
                // "non-null"/"not null"/"nonnull", and an always-`Bool(true)`
                // "alignment check" on "align") were DELETED: an unconstrained
                // fresh variable is always SAT and `Bool(true)` constrains
                // nothing, so both refuted a block harder the better its comment
                // was written. Test-only arm in any case (see the doc comment).
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe] SAFETY claim (unverified): {}",
                            claim.invariant,
                        ),
                    },
                    function: fn_sym.get_or_insert_with(|| func.name.as_str().into()).clone(),
                    location: block.span.clone(),
                    // Always SAT = conservatively "cannot verify".
                    // A downstream pass with actual program constraints can
                    // strengthen this into a real check.
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                });
            }
            _ => {
                // Trust (box-deref doc-lint fix): drop the always-`Bool(true)`
                // missing-SAFETY doc lint for a raw deref of a COMPILER-SYNTHESIZED
                // Box pointer (ElaborateBoxDerefs / box drop-glue Transmute of a
                // Box's Unique.NonNull field), whose span the compiler collected.
                // DROP-ONLY: this drops the documentation lint and nothing else.
                // The deref's validity is the separation engine's question
                // (`[unsafe:sep:deref]` rows), and since 2026-09-23 it declines
                // to charge ONLY a box it can root at a parameter or an in-body
                // `Box::new` (`sep_engine::validity_rooted_box_deref_ops`); every
                // other box deref keeps those rows. (`synthetic_nonmodeled_unsafe_
                // op_vcs`, once named here, covers union fields and mutable/extern
                // statics, not raw derefs.)
                // Excludes first-party mem::transmute-of-NonNull derefs (bare NonNull
                // source, never collected). The cross-file guard above catches
                // inlined CALLEE-file unsafe; this catches the box deref whose span
                // is the caller's OWN token (same file → the file guard misses it).
                //
                // THE KEY IS THE MIR OPERATION, NOT THE SPAN (2026-09-20).
                // `SourceSpan` discards the `SyntaxContext`, so under a
                // proc-macro `Span::call_site()` every operation of the
                // expansion carries ONE span and a span-keyed set could not say
                // WHICH operation the compiler collected. MEASURED on the sealed
                // `trustc ff538f905` (`$TMPDIR/rc4/boxcollide.rs` via `pm6`: a
                // builtin `Box` autoderef beside `mem::zeroed::<&'static u64>()`
                // and a `&*q` reborrow, all at `call_site()`): the plain-source
                // control minted TWO `[unsafe] missing SAFETY comment` rows and
                // the macro lane minted NO `hardened_unsafe_operation` row at
                // all. The compiler now collects `(BlockId, statement index)`
                // pairs (`collect_synthesized_box_deref_ops`), which name the
                // operation exactly — blocks and statements are extracted 1:1
                // (`trust_mir_extract::convert`: `BlockId(bb.as_usize())`, a
                // `.map()` over `bb_data.statements`), so the two sides index
                // the same body.
                //
                // The shape re-check stays, and is now a BELT rather than the
                // load-bearing narrowing: if block/statement numbering ever
                // diverges the key simply misses and the site KEEPS its
                // stand-in (fail-closed). A call terminator has no statement
                // index and can never be nominated.
                if let UnsafeOrigin::RawDeref { stmt } = block.origin
                    && box_deref_ops.contains(&(block.block_id, stmt))
                    // Every raw deref of the statement must be a synthesized box
                    // pointer (2026-10-09): `(*raw) = copy (*_t)` keeps its row.
                    && statement_synthesized_box_ptr_derefs(func, block.block_id, stmt).is_some()
                {
                    continue;
                }

                // OP-IDENTITY SUPERSESSION (sound): a scalar-index slice
                // `get_unchecked` block's COMPLETE UB set is exactly `index < len`,
                // for which the separation engine emits a real, discharge-able
                // `VcKind::UncheckedIndexBounds` obligation. That real obligation
                // supersedes this always-`Bool(true)` stand-in row for THIS block.
                // Keyed on the block's own terminator identity (NOT span
                // co-location), so a co-located/inlined non-bounds unsafe op — which
                // occupies its own MIR block — keeps its fail-closed row. An
                // UNGUARDED index still fails on the real `index >= len` obligation.
                // The shape predicate alone was a PREDICTION of that row; the row is
                // now also REQUIRED to have been minted for this block's terminator
                // (`sep_unchecked_index_sites`, recorded from the engine's own
                // output), so a body the engine declined keeps its stand-in — in a
                // SAFETY-declared block too (SAFETY-ASSUME-1: `decide_site` never
                // withholds a modeled operation's stand-in).
                if coverage.sep_unchecked_index_sites.contains(&block.block_id)
                    && block_is_bounds_complete_unchecked_index(func, block.block_id)
                {
                    continue;
                }

                let message = match decide_site(func, block, coverage) {
                    SiteDecision::Covered => continue,
                    // SAFETY-ASSUME-1: recorded by the declaration scope, charged by
                    // the compiler as the block's `assumption:safety-comment` row.
                    SiteDecision::Declared => continue,
                    SiteDecision::Refute(message) => message,
                    // THE stand-in — the production row for every site not
                    // decided above. Its message is byte-frozen (receipts). Do not
                    // "fix" it by reopening `span.file` through
                    // cwd/CARGO_MANIFEST_DIR: those ambient bytes are outside
                    // rustc's source dependency graph and previously suppressed
                    // this obligation via a same-named or edited file. Always SAT
                    // (`Bool(true)`) = always a finding.
                    SiteDecision::StandIn => MISSING_SAFETY_STANDIN_MSG.to_string(),
                };
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion { message },
                    function: fn_sym.get_or_insert_with(|| func.name.as_str().into()).clone(),
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

/// Is statement `stmt` of block `block_id` a raw dereference of the pointer the
/// compiler's `ElaborateBoxDerefs` / box drop glue synthesises — the vcgen-side
/// mirror of `collect_synthesized_box_deref_ops` (rustc_mir_transform/
/// trust_verify.rs), which admits ONLY the shape
/// `_p = Transmute(Copy|Move(<box>.0:Unique.0:NonNull)) as *T; … (*_p) …`?
///
/// Mirrored on the extracted MIR: the statement's rvalue or destination
/// dereferences local `_p` directly (its place is `*_p` or a projection under it); `_p` has EXACTLY
/// one whole-local definition in the body and no terminator writes it; that
/// definition is `Rvalue::Cast` — the extractor lowers a thin-pointer
/// `Transmute` to a value-preserving `Cast` (`convert.rs`, `CastKind::Transmute`)
/// — of a place whose last two projections are `Field(0)`, `Field(0)` and whose
/// remaining prefix is typed `alloc::boxed::Box` (sysroot-authenticated
/// spelling, so a stamped impersonator does not pass; a cut/compacted `Box`
/// arrives as a same-named `Ty::Datatype` marker and is accepted by name).
/// Every unmatched shape answers `false` and the site KEEPS its stand-in — the
/// fail-closed direction; the compiler's own span set is consulted first, so
/// this can only narrow that set, never widen it. It is the same belt, with the
/// same direction, in `sep_engine::validity_rooted_box_deref_ops`: there `false`
/// keeps the operation's `[unsafe:sep:*]` deref rows.
pub(crate) fn statement_derefs_synthesized_box_ptr(
    func: &VerifiableFunction,
    block_id: BlockId,
    stmt: usize,
) -> bool {
    let Some(mir) = block_by_id(func, block_id) else { return false };
    let Some(Statement::Assign { place: dest, rvalue, .. }) = mir.stmts.get(stmt) else {
        return false;
    };
    let read = match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::Ref { place, .. }
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    };
    // The destination counts as well as the read (2026-10-01): a safe
    // `(*box).f = v` writes through the same minted pointer, mirroring the
    // compiler's `collect_synthesized_box_deref_ops`.
    read.is_some_and(|place| place_derefs_synthesized_box_ptr(func, place))
        || place_derefs_synthesized_box_ptr(func, dest)
}

/// Does `place` dereference, as its first projection, the raw pointer
/// rustc's `ElaborateBoxDerefs` minted for a safe `*box`? The shape test of
/// [`statement_derefs_synthesized_box_ptr`].
fn place_derefs_synthesized_box_ptr(func: &VerifiableFunction, place: &Place) -> bool {
    matches!(place.projections.first(), Some(Projection::Deref))
        && local_is_synthesized_box_ptr(func, place.local)
}

/// Trust (2026-10-09): every place of statement `stmt` that dereferences a
/// pointer — its destination and every operand or place of its rvalue — when
/// EACH such leading deref is of a compiler-synthesized box pointer
/// ([`local_is_synthesized_box_ptr`]) and no deeper `Deref` occurs; the
/// synthesized pointer locals, deduplicated. `None` when the statement derefs
/// anything else (a genuine raw pointer, a `Deref` below the first projection)
/// or derefs nothing: such a statement is never treated as a safe `*box` as a
/// whole, so a genuine raw deref sharing it keeps its lint and rows.
pub(crate) fn statement_synthesized_box_ptr_derefs(
    func: &VerifiableFunction,
    block_id: BlockId,
    stmt: usize,
) -> Option<Vec<usize>> {
    let mir = block_by_id(func, block_id)?;
    let Some(Statement::Assign { place: dest, rvalue, .. }) = mir.stmts.get(stmt) else {
        return None;
    };
    if !matches!(
        rvalue,
        Rvalue::Use(_)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::Cast(_, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::BinaryOp(_, _, _)
            | Rvalue::CheckedBinaryOp(_, _, _)
            | Rvalue::UncheckedBinaryOp(_, _, _)
            | Rvalue::Aggregate(_, _)
            | Rvalue::Ref { .. }
            | Rvalue::CopyForDeref(_)
            | Rvalue::Len(_)
            | Rvalue::Discriminant(_)
    ) {
        return None;
    }
    let mut temps = Vec::new();
    let mut check_place = |place: &Place| -> bool {
        let Some(first_deref) =
            place.projections.iter().position(|p| matches!(p, Projection::Deref))
        else {
            return true;
        };
        if first_deref != 0
            || place.projections[1..].iter().any(|p| matches!(p, Projection::Deref))
            || !local_is_synthesized_box_ptr(func, place.local)
        {
            return false;
        }
        if !temps.contains(&place.local) {
            temps.push(place.local);
        }
        true
    };
    let check_op = |op: &Operand, check_place: &mut dyn FnMut(&Place) -> bool| -> bool {
        match op {
            Operand::Copy(p) | Operand::Move(p) => check_place(p),
            _ => true,
        }
    };
    if !check_place(dest) {
        return None;
    }
    let rvalue_ok = match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            check_op(op, &mut check_place)
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => {
            check_op(a, &mut check_place) && check_op(b, &mut check_place)
        }
        Rvalue::Aggregate(_, ops) => ops.iter().all(|op| check_op(op, &mut check_place)),
        Rvalue::Ref { place, .. }
        | Rvalue::CopyForDeref(place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place) => check_place(place),
        // Any other rvalue may carry a deref this census does not read.
        _ => false,
    };
    (rvalue_ok && !temps.is_empty()).then_some(temps)
}

/// Is `ptr_local` the raw pointer `ElaborateBoxDerefs` mints for a safe `*box`:
/// a `Ty::RawPtr` local with exactly one whole-local definition, no terminator
/// writing it, that definition a `Cast` of `<box>.0.0` where `<box>` is typed
/// `alloc::boxed::Box`? See [`statement_derefs_synthesized_box_ptr`].
pub(crate) fn local_is_synthesized_box_ptr(func: &VerifiableFunction, ptr_local: usize) -> bool {
    if !matches!(crate::local_ty_ref(func, ptr_local), Some(Ty::RawPtr { .. })) {
        return false;
    }
    // Exactly one whole-local definition, and no terminator destination.
    let mut def = None;
    if crate::any_local_write_candidate(func, &func.body.blocks, ptr_local, |b, item| match item {
        Some(s) => {
            if let Statement::Assign { place, rvalue, .. } = s
                && place.local == ptr_local
                && place.projections.is_empty()
            {
                if def.is_some() {
                    return true;
                }
                def = Some(rvalue);
            }
            false
        }
        None => matches!(
            &b.terminator,
            Terminator::Call { dest, .. } if dest.local == ptr_local && dest.projections.is_empty()
        ),
    }) {
        return false;
    }
    let Some(def) = def else { return false };
    let Rvalue::Cast(Operand::Copy(src) | Operand::Move(src), _) = def else { return false };
    let n = src.projections.len();
    // Trust (1.101): the cast operand is the box's `BoxRaw` field — ONE
    // trailing `Field(0)` whose place is typed `alloc::boxed::BoxRaw` — where
    // 1.99 spelled the `NonNull` two fields down. Either shape over a `Box`
    // base is the pass's temporary; anything else keeps its rows.
    let fields = if n >= 2
        && matches!(src.projections[n - 2], Projection::Field(0))
        && matches!(src.projections[n - 1], Projection::Field(0))
    {
        2
    } else if n >= 1
        && matches!(src.projections[n - 1], Projection::Field(0))
        && matches!(
            crate::place_ty_cow(func, src).as_deref(),
            Some(Ty::Adt { name, .. } | Ty::Datatype { name, .. })
                if name == "alloc::boxed::BoxRaw"
        )
    {
        1
    } else {
        return false;
    };
    matches!(
        crate::place_prefix_ty_cow(func, src.local, &src.projections[..n - fields]).as_deref(),
        Some(Ty::Adt { name, .. } | Ty::Datatype { name, .. }) if name == "alloc::boxed::Box"
    )
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
    if !crate::generate::terminator_presence_for(func).has_opaque {
        return Vec::new();
    }
    let mut vcs = Vec::new();
    let mut fn_sym: Option<trust_types::Symbol> = None;
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
                function: fn_sym.get_or_insert_with(|| func.name.as_str().into()).clone(),
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
    if !callee.contains("intrinsics::") {
        return None;
    }
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
/// obligation. Upstream 1.101: regenerated by the same rule (the parser
/// reproduces the 1.99 list exactly on the old tree). The `type_id*` family
/// moved to `core::intrinsics::reflection`, so those paths are no longer
/// direct children and decline at the leaf rule above — treated as unsafe,
/// the fail-closed side.
///
/// Sorted — [`is_safe_core_intrinsic`] binary-searches it, and
/// `safe_core_intrinsics_table_is_sorted` pins the ordering.
const SAFE_CORE_INTRINSICS: &[&str] = &[
    "abort_immediate",
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
    "cos",
    "ctlz",
    "ctpop",
    "cttz",
    "discriminant_value",
    "exp",
    "exp2",
    "fabs",
    "fadd_algebraic",
    "fdiv_algebraic",
    "field_offset",
    "field_representing_type_actual_type_id",
    "field_representing_type_name",
    "field_representing_type_offset",
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
    "integer_max",
    "integer_min",
    "is_val_statically_known",
    "likely",
    "log",
    "log10",
    "log2",
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
    "offload_get_num_devices",
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
    "sin",
    "size_of",
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
    "type_name",
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
///
/// UN-NAMESPACED LEAF NAMES, AND THE CALLER IS WHAT BOUNDS THEM (2026-09-20).
/// This table is also the compiler's suppression list for its
/// `[unsafe:unmodeled-call]` row, and it is reached there through
/// `crate::call_has_unsafe_model`. Both of the reasons it was allowed to stay a
/// bare name list have now been retired, in the two commits that had to retire
/// them:
///
/// * it "can never mint a proof, only SUPPRESS the compiler's refuting row,
///   which the mint answers with the fail-closed stand-in" — TRUE, and it was
///   never the whole story: the compiler evaluates this list on
///   `safe_def_path_str(tcx, did)`, which for a LOCAL callee is THE USER'S OWN
///   PATH, so a user who named a method `set_len` withheld the completeness
///   obligation from their own `unsafe fn` call. The suppression IS the defect.
/// * it was "one of the two belts that keep the compiler/vcgen MIRROR
///   fail-closed" — there is no mirror. `decide_site` is handed the compiler's
///   own rows (`UnsafeCoverage::compiler_unmodeled_call_blocks`) and predicts
///   nothing, so nothing here has to stay unanchored to keep a prediction
///   conservative.
///
/// What bounds the list now is its CALLER:
/// [`crate::call_has_unsafe_model_keyed`] consults the text ONLY for a callee
/// whose defining crate is the compiler's own sysroot (artifact residency), and
/// only on the bare definition path of that crate's own item. A user path never
/// reaches these bytes. The list is left un-namespaced deliberately — it is a
/// list of SYSROOT LEAF NAMES applied to sysroot definition paths, and anchoring
/// it would change which genuine sysroot items keep their stand-in without
/// closing anything that the caller's gate has not already closed.
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
    if contains_ascii_case_insensitive(callee, "ptr::")
        && ["ptr::read", "ptr::write", "ptr::copy", "ptr::swap", "ptr::replace", "ptr::drop_in_place"]
            .iter()
            .any(|p| contains_ascii_case_insensitive(callee, p))
    {
        return true;
    }
    if contains_ascii_case_insensitive(callee, "mem::")
        && ["mem::transmute", "mem::zeroed", "mem::uninitialized"]
            .iter()
            .any(|p| contains_ascii_case_insensitive(callee, p))
    {
        return true;
    }
    if contains_ascii_case_insensitive(callee, "alloc::")
        && ["alloc::alloc", "alloc::dealloc", "alloc::realloc"]
            .iter()
            .any(|p| contains_ascii_case_insensitive(callee, p))
    {
        return true;
    }
    if contains_ascii_case_insensitive(callee, "_unchecked")
        && [
            "get_unchecked",
            "new_unchecked",
            "unreachable_unchecked",
            "from_u32_unchecked",
            "str::from_utf8_unchecked",
            "from_bytes_with_nul_unchecked",
        ]
        .iter()
        .any(|p| contains_ascii_case_insensitive(callee, p))
    {
        return true;
    }
    if contains_ascii_case_insensitive(callee, "from_raw_parts")
        && (contains_ascii_case_insensitive(callee, "slice::from_raw_parts")
            || contains_ascii_case_insensitive(callee, "string::from_raw_parts"))
    {
        return true;
    }
    contains_ascii_case_insensitive(callee, "assume_init")
        || contains_ascii_case_insensitive(callee, "set_len")
}

fn contains_ascii_case_insensitive(s: &str, needle: &str) -> bool {
    let h = s.as_bytes();
    let n = needle.as_bytes();
    n.is_empty() || h.windows(n.len()).any(|w| w.eq_ignore_ascii_case(n))
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
