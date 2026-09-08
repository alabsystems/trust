//! Shared TERMINATOR-obligation recognizers — one definition, two producers.
//!
//! trust-vcgen's `v2_build_terminator_vc` (generate/overflow_vc.rs) mints the
//! `VcKind::Unreachable` rows for bare `Terminator::Unreachable` blocks and for
//! the panic-call shapes that lower from `unreachable!()`; the trust-ir spine's
//! `generate_native_safety_vcs` must derive the SAME rows or every function
//! carrying one lands in the producer-disagreement bucket
//! (`NativeGenOutcome::Disagreed`, class `Unreachable` — measured 273 functions
//! with 0 native on the 2026-09-01 scorecard artifact).
//!
//! This module is the `trust_types::static_truth` move applied to those
//! recognizers, for the same reason recorded there: two copies of a rule that
//! must agree make any drift surface as a PHANTOM disagreement — an alarm about
//! the checkers disagreeing rather than about a hole in the checking. One
//! definition, two callers (`crates/trust-vcgen/src/generate/overflow_vc.rs`
//! and `crates/trust-ir-bridge/src/lower.rs`).
//!
//! What is deliberately NOT here: the REACHABILITY gate. trust-vcgen mints a
//! terminator VC only for blocks its path-guard walk reached from the entry
//! (`generate/safety.rs` arm 1b — dead scaffolding blocks must not be falsely
//! refuted), and that walk (budgets, collapse modes, guard versioning) is
//! vcgen's own analysis. A consumer that needs the same population takes it as
//! an INPUT (`trust_vcgen::terminator_vc_block_set`), it does not re-derive it.

use crate::{
    BasicBlock, BlockId, ConstValue, Operand, SourceSpan, Statement, Terminator, VerifiableFunction,
};

/// The successor blocks of `terminator` — moved verbatim from trust-vcgen's
/// `v2_terminator_targets` (generate/assert_refutation.rs), which now
/// delegates here.
#[must_use]
pub fn terminator_targets(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut blocks = targets.iter().map(|(_, target)| *target).collect::<Vec<_>>();
            blocks.push(*otherwise);
            blocks
        }
        Terminator::Call { target: Some(target), .. } => vec![*target],
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        Terminator::Return | Terminator::Call { target: None, .. } | Terminator::Unreachable => {
            vec![]
        }
        _ => vec![],
    }
}

/// The span a block-level obligation reports: the block's first `Assign`
/// statement's span, else the function's. Moved verbatim from trust-vcgen's
/// `v2_block_span` (generate/block_defs.rs), which now delegates here.
#[must_use]
pub fn block_span(func: &VerifiableFunction, block: &BasicBlock) -> SourceSpan {
    block
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            Statement::Assign { span, .. } => Some(span.clone()),
            _ => None,
        })
        .unwrap_or_else(|| func.span.clone())
}

/// Whether `callee` is the typed `unreachable!("{}")` display entrypoint.
/// Moved verbatim from trust-vcgen's `v2_is_unreachable_panic_call`.
#[must_use]
pub fn is_unreachable_panic_call(callee: &str) -> bool {
    callee.contains("unreachable_display")
}

/// Whether `callee` is a user `assert!`/`panic!`-family panic entrypoint.
/// Moved verbatim from trust-vcgen's `v2_is_assertion_panic_call`.
#[must_use]
pub fn is_assertion_panic_call(callee: &str) -> bool {
    callee.contains("begin_panic")
        || callee.contains("panic_fmt")
        || callee.contains("panic_display")
        || callee.contains("assert_failed")
}

/// The bare panic intrinsic `core::panicking::panic` lowers BOTH
/// `unreachable!()` and `assert!(cond)` / `panic!("static str")`, distinguished
/// only by the static message. Match the well-known sentinel; wording drift
/// fails CLOSED (no VC — never a false-prove). Moved verbatim from
/// trust-vcgen's `v2_is_unreachable_sentinel_panic`.
#[must_use]
pub fn is_unreachable_sentinel_panic(callee: &str, args: &[Operand]) -> bool {
    if !callee.ends_with("::panic") {
        return false;
    }
    args.iter()
        .any(|a| operand_str_constant(a).is_some_and(|s| s.contains("entered unreachable code")))
}

/// Whether `block` is reached (transitively, through plain control flow)
/// from a from-str-nonconst / unreachable-display panic call — the chain
/// classification that turns a panic-call obligation from `Assertion` into
/// `Unreachable`. Moved verbatim from trust-vcgen's
/// `v2_is_unreachable_panic_chain`.
#[must_use]
pub fn is_unreachable_panic_chain(func: &VerifiableFunction, block_id: BlockId) -> bool {
    fn dfs(
        func: &VerifiableFunction,
        block_id: BlockId,
        seen: &mut std::collections::HashSet<BlockId>,
    ) -> bool {
        if !seen.insert(block_id) {
            return false;
        }

        for pred in func
            .body
            .blocks
            .iter()
            .filter(|bb| terminator_targets(&bb.terminator).contains(&block_id))
        {
            match &pred.terminator {
                Terminator::Call { func: callee, .. }
                    if callee.contains("from_str_nonconst")
                        || callee.contains("unreachable_display") =>
                {
                    return true;
                }
                Terminator::Call { target: Some(_), .. }
                | Terminator::Goto(_)
                | Terminator::Drop { .. }
                | Terminator::Opaque { .. }
                    if dfs(func, pred.id, seen) =>
                {
                    return true;
                }
                _ => {}
            }
        }

        false
    }

    dfs(func, block_id, &mut std::collections::HashSet::new())
}

/// `Some(span)` exactly when trust-vcgen's `v2_build_terminator_vc` would mint
/// a `VcKind::Unreachable` VC for this block (formula `Bool(true)`, function =
/// the func's name) — arm for arm, in its arm ORDER, restricted to the
/// Unreachable-classified outcomes. The `Assertion`-classified panic-call
/// outcomes stay vcgen-local (their message rendering is not an obligation
/// identity this comparison ranges over).
///
/// The caller supplies the reachability gate (see the module doc): this
/// function answers the SHAPE question only.
#[must_use]
pub fn unreachable_terminator_span(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Option<SourceSpan> {
    match &block.terminator {
        Terminator::Unreachable => Some(block_span(func, block)),
        Terminator::Call { func: callee, span, .. } if is_unreachable_panic_call(callee) => {
            Some(span.clone())
        }
        Terminator::Call { func: callee, args, span, .. }
            if is_unreachable_sentinel_panic(callee, args) =>
        {
            if is_unreachable_panic_chain(func, block.id) { Some(span.clone()) } else { None }
        }
        Terminator::Call { func: callee, span, .. } if is_assertion_panic_call(callee) => {
            if is_unreachable_panic_chain(func, block.id) {
                Some(span.clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The UTF-8 contents of a `&str` constant operand, if `op` is one. Local
/// helper for the sentinel recognizer (trust-vcgen keeps its own copy for its
/// other template/decoder uses).
fn operand_str_constant(op: &Operand) -> Option<String> {
    match op {
        Operand::Constant(ConstValue::Str { bytes }) => {
            Some(String::from_utf8_lossy(bytes).into_owned())
        }
        _ => None,
    }
}
