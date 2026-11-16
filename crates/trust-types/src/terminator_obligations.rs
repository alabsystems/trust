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
    let mut blocks = Vec::new();
    for_each_terminator_target(terminator, |target| blocks.push(target));
    blocks
}

/// Visit every normal-flow successor block of `terminator` in [`terminator_targets`]
/// order without allocating a temporary `Vec<BlockId>`.
pub fn for_each_terminator_target(terminator: &Terminator, mut f: impl FnMut(BlockId)) {
    match terminator {
        Terminator::Goto(target)
        | Terminator::Call { target: Some(target), .. }
        | Terminator::Assert { target, .. }
        | Terminator::Drop { target, .. } => f(*target),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for &(_, target) in targets {
                f(target);
            }
            f(*otherwise);
        }
        Terminator::Opaque { targets, .. } => {
            for &target in targets {
                f(target);
            }
        }
        Terminator::Return | Terminator::Call { target: None, .. } | Terminator::Unreachable => {}
        _ => {}
    }
}

/// True when `needle` is one of [`terminator_targets`], without allocating a
/// temporary `Vec<BlockId>`.
#[must_use]
pub fn terminator_has_target(terminator: &Terminator, needle: BlockId) -> bool {
    match terminator {
        Terminator::Goto(target)
        | Terminator::Call { target: Some(target), .. }
        | Terminator::Assert { target, .. }
        | Terminator::Drop { target, .. } => *target == needle,
        Terminator::SwitchInt { targets, otherwise, .. } => {
            *otherwise == needle || targets.iter().any(|&(_, target)| target == needle)
        }
        Terminator::Opaque { targets, .. } => targets.contains(&needle),
        Terminator::Return | Terminator::Call { target: None, .. } | Terminator::Unreachable => {
            false
        }
        _ => false,
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

/// `core::hint::unreachable_unchecked` — reaching the call is undefined behaviour
/// by the callee's own contract, so the block that calls it owes EXACTLY the
/// obligation a bare `Terminator::Unreachable` owes: its path condition must be
/// unsatisfiable. Minting it here (the shared classifier) is what lets
/// `unsafe_verify::detection::generate_safety_vcs` retire the always-`Bool(true)`
/// stand-in row for that call: the `VcKind::Unreachable` row a solver can prove
/// or refute on the block's real path guards replaces it.
///
/// EXACT, SYSROOT-AUTHENTICATED spelling. The extractor renders a callee under a
/// sysroot-looking crate name that is NOT the real sysroot with the
/// `TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX` stamp
/// (`trust_mir_extract::convert::direct_call_def_path`), which breaks this
/// prefix match — a forged `core::hint::unreachable_unchecked` therefore keeps
/// its fail-closed stand-in. The item has no generic parameters, so the only
/// admitted continuations are the empty string and a turbofish/fingerprint
/// suffix; `core::hint::unreachable_unchecked_foo` is NOT matched.
#[must_use]
pub fn is_unreachable_unchecked_call(callee: &str) -> bool {
    const PATH: &str = "core::hint::unreachable_unchecked";
    match callee.strip_prefix(PATH) {
        Some("") => true,
        Some(rest) => rest.starts_with("::<") || rest.starts_with('<'),
        None => false,
    }
}

/// The upstream panic-outlining change (rust-lang/rust#163766) makes the
/// no-argument `unreachable!()` / `panic!()` / `unimplemented!()` / `todo!()`
/// forms call per-macro outlined entrypoints in `core::panicking` —
/// `unreachable_default_msg`, `panic_default_msg`, `unimplemented_default_msg`,
/// `todo_default_msg` — instead of inlining a call to `core::panicking::panic`
/// with the fixed message at every site. These are the same panic entrypoints
/// under a name the pre-existing shape recognizers do not know; without the
/// predicates below the call sites silently stop being minted (the name-match
/// drift would fail OPEN on the census, not closed). Exact, sysroot-
/// authenticated spelling on the `is_unreachable_unchecked_call` discipline:
/// the items have no generic parameters, so the only admitted continuations
/// are the empty string and a turbofish/fingerprint suffix.
fn is_exact_core_panicking_rest(rest: &str, item: &str) -> bool {
    let Some(rest) = rest.strip_prefix(item) else { return false };
    rest.is_empty() || rest.starts_with("::<") || rest.starts_with('<')
}

fn is_exact_core_panicking(callee: &str, item: &str) -> bool {
    let Some(rest) = callee.strip_prefix("core::panicking::") else { return false };
    is_exact_core_panicking_rest(rest, item)
}

/// Whether `callee` is the outlined `unreachable!()` entrypoint
/// `core::panicking::unreachable_default_msg` — the post-outlining spelling of
/// the same call `is_unreachable_sentinel_panic` matches through the message.
#[must_use]
pub fn is_unreachable_default_msg_call(callee: &str) -> bool {
    is_exact_core_panicking(callee, "unreachable_default_msg")
}

/// Whether `callee` is one of the outlined bare-macro panic entrypoints —
/// the post-outlining spelling of `core::panicking::panic` reached with the
/// fixed default message from `panic!()` / `unimplemented!()` / `todo!()`.
#[must_use]
pub fn is_bare_default_msg_panic_call(callee: &str) -> bool {
    let Some(rest) = callee.strip_prefix("core::panicking::") else { return false };
    is_exact_core_panicking_rest(rest, "panic_default_msg")
        || is_exact_core_panicking_rest(rest, "unimplemented_default_msg")
        || is_exact_core_panicking_rest(rest, "todo_default_msg")
}

/// The fixed panic message an outlined default-message entrypoint raises —
/// the same string the pre-outlining expansion passed to
/// `core::panicking::panic` at the call site, so message-keyed consumers
/// (contract-panic payload harvesting) see the same constants.
#[must_use]
pub fn default_msg_panic_message(callee: &str) -> Option<&'static str> {
    let rest = callee.strip_prefix("core::panicking::")?;
    if is_exact_core_panicking_rest(rest, "unreachable_default_msg") {
        Some("internal error: entered unreachable code")
    } else if is_exact_core_panicking_rest(rest, "panic_default_msg") {
        Some("explicit panic")
    } else if is_exact_core_panicking_rest(rest, "unimplemented_default_msg") {
        Some("not implemented")
    } else if is_exact_core_panicking_rest(rest, "todo_default_msg") {
        Some("not yet implemented")
    } else {
        None
    }
}

/// Whether `callee` has the bare-panic call shape — the historical loose
/// `::panic` suffix (the pre-outlining `core::panicking::panic` and any
/// same-suffix entrypoint) unioned with the outlined default-message
/// entrypoints, `unreachable!()` sentinel included. This is the shape set the
/// suffix matched before the outlining change; consumers that must exclude
/// the sentinel keep doing so through `is_unreachable_sentinel_panic`.
#[must_use]
pub fn is_bare_panic_call(callee: &str) -> bool {
    callee.ends_with("::panic")
        || is_bare_default_msg_panic_call(callee)
        || is_unreachable_default_msg_call(callee)
}

/// Whether `callee` is a user `assert!`/`panic!`-family panic entrypoint.
/// Moved verbatim from trust-vcgen's `v2_is_assertion_panic_call`.
#[must_use]
pub fn is_assertion_panic_call(callee: &str) -> bool {
    if callee.contains("panic") {
        callee.contains("begin_panic")
            || callee.contains("panic_fmt")
            || callee.contains("panic_display")
            || callee.contains("assert_failed")
    } else {
        callee.contains("assert_failed")
    }
}

/// The bare panic intrinsic `core::panicking::panic` lowers BOTH
/// `unreachable!()` and `assert!(cond)` / `panic!("static str")`, distinguished
/// only by the static message. Match the well-known sentinel; wording drift
/// fails CLOSED (no VC — never a false-prove). The no-argument `unreachable!()`
/// form lowers to the outlined `unreachable_default_msg` entrypoint instead
/// (see the predicates above) and is the same sentinel by name. Moved
/// verbatim from trust-vcgen's `v2_is_unreachable_sentinel_panic`.
#[must_use]
pub fn is_unreachable_sentinel_panic(callee: &str, args: &[Operand]) -> bool {
    if is_unreachable_default_msg_call(callee) {
        return true;
    }
    if !callee.ends_with("::panic") {
        return false;
    }
    args.iter().any(|a| {
        matches!(
            a,
            Operand::Constant(ConstValue::Str { bytes })
                if String::from_utf8_lossy(bytes).contains("entered unreachable code")
        )
    })
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
        seen: &mut crate::fx::FxHashSet<BlockId>,
    ) -> bool {
        if !seen.insert(block_id) {
            return false;
        }

        for pred in func
            .body
            .blocks
            .iter()
            .filter(|bb| terminator_has_target(&bb.terminator, block_id))
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

    dfs(func, block_id, &mut crate::fx::FxHashSet::default())
}

/// Structural classification of a block terminator's obligation shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminatorObligationShape {
    /// Mints a `VcKind::Unreachable` obligation at `span`.
    Unreachable(SourceSpan),
    /// Mints a `VcKind::Assertion` panic-call obligation at `span`.
    AssertionPanicCall(SourceSpan),
}

/// Classify `block.terminator` into its obligation shape (`Unreachable` vs
/// `AssertionPanicCall`) in a single pass, avoiding duplicate panic-call
/// string scans when `v2_build_terminator_vc` handles non-unreachable-chain
/// assertion panics.
#[must_use]
pub fn classify_terminator_obligation(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Option<TerminatorObligationShape> {
    match &block.terminator {
        Terminator::Unreachable => {
            Some(TerminatorObligationShape::Unreachable(block_span(func, block)))
        }
        // `hint::unreachable_unchecked()`: UB iff reachable — the same obligation
        // as a bare `Unreachable`, keyed on the call's own span. See
        // [`is_unreachable_unchecked_call`].
        Terminator::Call { func: callee, span, .. } if is_unreachable_unchecked_call(callee) => {
            Some(TerminatorObligationShape::Unreachable(span.clone()))
        }
        Terminator::Call { func: callee, span, .. } if is_unreachable_panic_call(callee) => {
            Some(TerminatorObligationShape::Unreachable(span.clone()))
        }
        Terminator::Call { func: callee, args, span, .. }
            if is_unreachable_sentinel_panic(callee, args) || is_assertion_panic_call(callee) =>
        {
            if is_unreachable_panic_chain(func, block.id) {
                Some(TerminatorObligationShape::Unreachable(span.clone()))
            } else {
                Some(TerminatorObligationShape::AssertionPanicCall(span.clone()))
            }
        }
        Terminator::Call { func: callee, span, .. } if is_bare_default_msg_panic_call(callee) => {
            Some(TerminatorObligationShape::AssertionPanicCall(span.clone()))
        }
        _ => None,
    }
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
    match classify_terminator_obligation(func, block) {
        Some(TerminatorObligationShape::Unreachable(span)) => Some(span),
        Some(TerminatorObligationShape::AssertionPanicCall(_)) | None => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn str_arg(s: &str) -> Operand {
        Operand::Constant(ConstValue::Str { bytes: s.as_bytes().to_vec() })
    }

    #[test]
    fn outlined_unreachable_is_the_sentinel() {
        assert!(is_unreachable_default_msg_call("core::panicking::unreachable_default_msg"));
        assert!(is_unreachable_sentinel_panic("core::panicking::unreachable_default_msg", &[]));
        assert_eq!(
            default_msg_panic_message("core::panicking::unreachable_default_msg"),
            Some("internal error: entered unreachable code")
        );
        // The pre-outlining spelling still classifies through the message.
        assert!(is_unreachable_sentinel_panic(
            "core::panicking::panic",
            &[str_arg("internal error: entered unreachable code")]
        ));
        assert!(!is_unreachable_sentinel_panic("core::panicking::panic", &[str_arg("boom")]));
    }

    #[test]
    fn bare_default_msg_family_and_messages() {
        for (callee, msg) in [
            ("core::panicking::panic_default_msg", "explicit panic"),
            ("core::panicking::unimplemented_default_msg", "not implemented"),
            ("core::panicking::todo_default_msg", "not yet implemented"),
        ] {
            assert!(is_bare_default_msg_panic_call(callee), "{callee}");
            assert!(!is_unreachable_default_msg_call(callee), "{callee}");
            assert_eq!(default_msg_panic_message(callee), Some(msg), "{callee}");
            assert!(!is_unreachable_sentinel_panic(callee, &[]), "{callee}");
        }
    }

    #[test]
    fn default_msg_matching_is_exact_and_authenticated() {
        // Sibling names and lookalike longer items never match.
        for callee in [
            "core::panicking::unreachable_default_msg_foo",
            "core::panicking::panic_default_msgr",
            "core::panicking::unreachable_display",
            // Forged sysroot-looking paths: not the exact core path.
            "mycrate::panicking::unreachable_default_msg",
            "alloc::panicking::panic_default_msg",
            "core::panicking2::unreachable_default_msg",
        ] {
            assert!(!is_unreachable_default_msg_call(callee), "forged/sibling matched: {callee}");
            assert!(!is_bare_default_msg_panic_call(callee), "forged/sibling matched: {callee}");
            assert_eq!(default_msg_panic_message(callee), None, "{callee}");
        }
        // The substring recognizers' prey stays theirs, not the exact matchers'.
        assert!(!is_bare_default_msg_panic_call("core::panicking::panic"));
        assert!(!is_unreachable_default_msg_call("core::hint::unreachable_unchecked"));
    }

    #[test]
    fn bare_panic_call_unions_old_and_outlined_shapes() {
        assert!(is_bare_panic_call("core::panicking::panic"));
        assert!(is_bare_panic_call("core::panicking::panic_default_msg"));
        assert!(is_bare_panic_call("core::panicking::unreachable_default_msg"));
        assert!(is_bare_panic_call("core::panicking::unimplemented_default_msg"));
        assert!(is_bare_panic_call("core::panicking::todo_default_msg"));
        // Forged paths reach the union only through the historical loose
        // suffix, never through the exact default-message arms.
        assert!(!is_bare_panic_call("mycrate::panicking::unreachable_default_msg"));
        assert!(!is_bare_panic_call("core::panicking::panic_fmt"));
        assert!(!is_bare_panic_call("core::hint::unreachable_unchecked"));
        assert!(is_assertion_panic_call("core::panicking::assert_failed::<u64, u64>"));
        assert!(is_assertion_panic_call("assert_failed"));
        assert!(is_assertion_panic_call("core::panicking::panic_fmt"));
        assert!(!is_assertion_panic_call("core::panicking::panic"));
    }
}
