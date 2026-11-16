// trust_vcgen/unsafe_verify: unsafe-operation detection and the unsafe obligation rows
//
// Detects each unsafe OPERATION in MIR (`detection::detect_unsafe_blocks`) and
// mints its per-site `[unsafe` assertion rows (`detection::generate_safety_vcs`,
// reached through `check_unsafe`, which `generate::entry` calls), plus the
// inline-asm rows (`detection::generate_inline_asm_vcs`, also called from
// `generate::entry`). What a site mints is decided per site by
// `detection::decide_site`; `generate_safety_vcs`'s doc has the rule and the
// measurements behind it.
//
// SAFETY comments are parsed (`parse_safety_comment`, `attach_safety_comments`),
// but vcgen has no source-map access: the one production caller passes NO
// comments, so no parsed safety claim reaches a VC today.
//
// SAFETY-ASSUME-1 (ruled 2026-10-17): the COMPILER reads the comments instead.
// It decides which MIR operations sit in a user `unsafe { }` block whose
// `// SAFETY:` comment is placed where `clippy::undocumented_unsafe_blocks`
// accepts one, and installs them through `safety_declared::
// with_safety_declared_unsafe_ops`. `detection::decide_site` withholds a call's
// stand-in and a raw reborrow's `[unsafe:reborrow]` row for those operations Trust
// does not model; a modeled call, or a raw-pointer read, whose row the engine did
// not mint keeps its FAILED stand-in. The scope records every site it withholds,
// and the compiler charges each such block one `assumption:safety-comment` row.
// No comment text reaches vcgen, and nothing here is ever counted proved.
//
// This module mints no pointer-alignment, provenance, transmute-layout or FFI
// pre/post-condition obligation of its own. The separation engine's
// `[unsafe:sep:*]` rows and the compiler's `[unsafe:unmodeled-call]` /
// `[unsafe:union-field]` / `[unsafe:mutable-static]` rows are minted elsewhere.
//
// Part of #79: Unsafe code verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::*;

pub(crate) mod detection;
pub(crate) mod safety_declared;
#[cfg(test)]
mod tests;

pub(crate) use detection::{attach_safety_comments, detect_unsafe_blocks, generate_safety_vcs};

// ────────────────────────────────────────────────────────────────────────────
// Core types
// ────────────────────────────────────────────────────────────────────────────

/// Which MIR construct a detected [`UnsafeBlock`] IS. Detection is per unsafe
/// OPERATION, never per source-level `unsafe { }`: an `UnsafeBlock` is either the
/// unsafe-signature / foreign / unsafe-named CALL that terminates a MIR block, or
/// one raw-pointer-dereferencing STATEMENT inside a block. This is what decides
/// (c) of the mint-side design: a source `unsafe { }` wrapping only safe code has
/// neither, is never detected, and owes nothing — see
/// `detection::generate_safety_vcs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnsafeOrigin {
    /// The block's terminator call. The two flags are the extractor's
    /// authoritative signals (`Terminator::Call::{is_unsafe_sig, is_foreign}`),
    /// copied so the mint can mirror the compiler's `[unsafe:unmodeled-call]`
    /// rule without re-reading the terminator. The operation's identity is
    /// `(block_id, MirOp::Terminator)` — a block has exactly one terminator.
    Call { is_unsafe_sig: bool, is_foreign: bool },
    /// A statement whose place or rvalue dereferences a raw pointer. `stmt` is
    /// its index in `block.stmts`, so the operation's identity is
    /// `(block_id, MirOp::Statement(stmt))`.
    RawDeref { stmt: usize },
}

/// One MIR operation inside a basic block: the `i`-th statement, or the
/// terminator. Paired with a `BlockId` this is the identity the mint keys
/// coverage on — the identity `SourceSpan` cannot provide, because
/// `SourceSpan` discards the `SyntaxContext` and a proc-macro expansion stamps
/// one `call_site()` span on every operation it emits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum MirOp {
    Statement(usize),
    Terminator,
}

/// An unsafe block discovered in MIR, with its optional safety claim.
#[derive(Debug, Clone)]
pub(crate) struct UnsafeBlock {
    /// Source location of the unsafe block.
    pub(crate) span: SourceSpan,
    /// The raw `// SAFETY:` comment text, if found.
    pub(crate) safety_comment: Option<String>,
    /// Parsed safety claim, if the comment was successfully parsed.
    pub(crate) safety_claim: Option<SafetyClaim>,
    /// The block index in MIR where the unsafe code lives.
    pub(crate) block_id: BlockId,
    /// Which construct in that block this is (call terminator vs deref statement).
    pub(crate) origin: UnsafeOrigin,
}

/// The behavioural obligations ALREADY minted for this body by the lanes that
/// run before `check_unsafe`, keyed the way the mint needs them. This is
/// analysis-output disclosure, not proof authority: an entry here can only
/// SUPPRESS the always-`Bool(true)` stand-in row for a site that carries a real
/// obligation; nothing in it is ever assumed true.
///
/// KEYED ON THE MIR OPERATION, NEVER ON A SPAN. The separation engine reports,
/// for every row it mints, the `(block, MirOp)` it was interpreting at the time
/// (`sep_engine::check_sep_unsafe_blocked_ops`), and that pair is what is
/// indexed here. A `(block, span)` key was tried and REFUTED: `SourceSpan`
/// discards the `SyntaxContext`, so under a proc-macro `Span::call_site()` a
/// deref STATEMENT's `[unsafe:sep:deref]` rows carried the same key as the
/// `mem::zeroed::<&T>()` CALL terminator of the same block and "covered" it,
/// and a `ptr::read` CALL's rows carried the same key as a deref statement.
///
/// `Default` is EMPTY, and empty is the fail-closed direction: with no coverage
/// every detected site keeps its stand-in exactly as before.
#[derive(Debug, Default, Clone)]
pub(crate) struct UnsafeCoverage {
    /// The blocks whose TERMINATOR the separation engine was interpreting when
    /// it minted an `[unsafe:sep:*]` row — i.e. the call terminators that carry
    /// a behavioural row of their own. A row minted for a statement of the same
    /// block is NOT in here, whatever its span.
    pub(crate) sep_call_sites: FxHashSet<BlockId>,
    /// The `(block, statement index)` of every STATEMENT the engine was
    /// interpreting when it minted a `[unsafe:sep:deref]` row — the family it
    /// mints for a raw-pointer dereference statement. A deref statement is
    /// covered only by a deref-family row minted for THAT statement; a row
    /// minted for the block's terminator (`ptr::read`/`ptr::write`, which mint
    /// the same family) is not in here.
    pub(crate) sep_deref_sites: FxHashSet<(BlockId, usize)>,
    /// The blocks whose TERMINATOR the engine was interpreting when it minted a
    /// `VcKind::UncheckedIndexBounds` row — the real `index < len` obligation of
    /// a `get_unchecked` call. `block_is_bounds_complete_unchecked_index` used to
    /// PREDICT that row from the callee's shape; the prediction is now
    /// confirmed against this set, so a body the engine declined
    /// (`has_unsafe_patterns`, a budget) or a callee spelling the engine's own
    /// recognizer does not match keeps its stand-in.
    pub(crate) sep_unchecked_index_sites: FxHashSet<BlockId>,
    /// The blocks the path-guard walk reached from the entry — EXACTLY the
    /// population over which `generate::safety` arm 1b mints terminator VCs
    /// (`VcKind::Unreachable` included). A block outside it may be dead or may
    /// be budget-collapsed; either way no `Unreachable` row was minted for it,
    /// so its stand-in is kept.
    pub(crate) reached_blocks: FxHashSet<BlockId>,
    /// THE COMPILER'S OWN `[unsafe:unmodeled-call]` ROWS, by the MIR block each
    /// was minted for — installed by `rustc_mir_transform::trust_verify` through
    /// [`crate::VcgenContext::with_compiler_unmodeled_call_blocks`] from the row
    /// set it generated over THIS body, before this generation ran.
    ///
    /// This is POSITIVE EVIDENCE and it replaces a bet. Until 2026-09-20
    /// `decide_site` dropped a call site's fail-closed stand-in whenever a
    /// vcgen-side PREDICTOR said the compiler would mint that row; the predictor
    /// mirrored a string predicate the compiler evaluates on a different
    /// spelling of the same callee, and a disagreement in the direction that
    /// says "unmodeled here, modeled there" deleted the stand-in and got
    /// nothing in return — an unsafe site with ZERO obligations. A row that is
    /// in this set EXISTS; one that is not, does not.
    ///
    /// EMPTY IS FAIL-CLOSED, and empty is what every caller that is not the
    /// compiler supplies.
    pub(crate) compiler_unmodeled_call_blocks: FxHashSet<BlockId>,
    /// Trust (G1, 2026-10-27): the `mem::zeroed::<T>()` call blocks whose `T` the
    /// COMPILER found zero-valid by rustc's exact layout validity check, installed
    /// through [`crate::VcgenContext::with_compiler_zero_valid_zeroed_blocks`]. Empty
    /// (every non-compiler caller) admits nothing beyond the structural verdict.
    pub(crate) compiler_zero_valid_zeroed_blocks: FxHashSet<BlockId>,
    /// Trust (AW-1, 2026-10-03): the call blocks the COMPILER identified as
    /// rustc's own `.await` lowering (`Pin::new_unchecked(&mut __awaitee)`,
    /// `get_context(_task_context)`), installed through
    /// [`crate::VcgenContext::with_await_desugared_unsafe_call_blocks`]. A
    /// `UnsafeOrigin::Call` site in here owes no SAFETY-comment stand-in: the
    /// user did not write it and cannot annotate it. EMPTY IS FAIL-CLOSED.
    pub(crate) await_desugared_unsafe_call_blocks: FxHashSet<BlockId>,
}

impl UnsafeCoverage {
    /// Index one separation-engine row by the `(block, op)` the engine was
    /// interpreting when it minted it.
    pub(crate) fn record_sep_row(&mut self, vc: &VerificationCondition, block: BlockId, op: MirOp) {
        if let (VcKind::UncheckedIndexBounds { .. }, MirOp::Terminator) = (&vc.kind, op) {
            self.sep_unchecked_index_sites.insert(block);
            return;
        }
        let VcKind::Assertion { message } = &vc.kind else { return };
        if !message.starts_with(VcKind::SEP_UNSAFE_ASSERTION_PREFIX) {
            return;
        }
        match op {
            MirOp::Terminator => {
                self.sep_call_sites.insert(block);
            }
            MirOp::Statement(idx) => {
                if message.starts_with("[unsafe:sep:deref]") {
                    self.sep_deref_sites.insert((block, idx));
                }
            }
        }
    }
}

/// A structured safety claim extracted from a `// SAFETY:` comment.
///
/// Convention: Rust's `// SAFETY:` comments should state:
/// 1. The invariant that makes this unsafe code sound.
/// 2. The justification for why that invariant holds at this call site.
///
/// We parse these into structured form so the solver can attempt to verify
/// the claimed invariant against the surrounding code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SafetyClaim {
    /// The invariant being claimed (e.g., "pointer is non-null and aligned").
    pub(crate) invariant: String,
    /// The justification for why the invariant holds (e.g., "checked above on line 42").
    pub(crate) justification: String,
}

// ────────────────────────────────────────────────────────────────────────────
// Entry point
// ────────────────────────────────────────────────────────────────────────────

/// Top-level entry point: check a function for unsafe code and generate VCs.
///
/// Called from `generate::entry`. Detects unsafe blocks, attaches
/// safety comments (when available), and generates assertion VCs.
pub(crate) fn check_unsafe(
    func: &VerifiableFunction,
    comments: &[(SourceSpan, String)],
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
    coverage: &UnsafeCoverage,
    vcs: &mut Vec<VerificationCondition>,
) {
    let mut blocks = detect_unsafe_blocks(func);
    if blocks.is_empty() {
        return;
    }

    attach_safety_comments(&mut blocks, comments);
    let safety_vcs = generate_safety_vcs(func, &blocks, box_deref_ops, coverage);
    vcs.extend(safety_vcs);
}
