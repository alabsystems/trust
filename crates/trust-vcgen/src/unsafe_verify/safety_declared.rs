// trust_vcgen/unsafe_verify/safety_declared: the SAFETY-comment declaration scope
//
// Trust (SAFETY-ASSUME-1, ruled 2026-10-17; docs/DECISION_QUEUE.md
// "SAFETY-ASSUME-1"). A user-written `unsafe { }` block whose `// SAFETY:`
// comment sits where `clippy::undocumented_unsafe_blocks` accepts one is a
// DECLARED ASSUMPTION: its unmodeled unsafe-operation rows are withheld and the
// compiler charges ONE `assumption:safety-comment` row per block instead
// (`rustc_mir_transform::trust_verify::safety_comment_assumption`). Only the
// compiler can decide which operations qualify — it alone holds the HIR block,
// the source map and the MIR operation identity together — so it hands the
// decision in here, keyed on the operation (never on a span), and reads back
// exactly which of those operations this generation withheld.
//
// THE INVARIANT: an operation is withheld ONLY when this scope RECORDS it.
// `withhold_declared_site` is the one entry, it records before it answers
// `true`, and the compiler charges a row for every block one of whose recorded
// operations it declared. So a withheld row never vanishes without its
// assumption row, whichever vcgen frame or regeneration minted it. A generation
// outside any scope, or for another body, withholds nothing: every site keeps
// its fail-closed row.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cell::RefCell;

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{BlockId, SourceSpan, VerifiableFunction};

use super::{UnsafeBlock, UnsafeOrigin};

/// The MIR operations of ONE body that sit inside a user-written `unsafe { }`
/// block carrying a clippy-placed `// SAFETY:` comment, as the COMPILER decided
/// them over the very body the function was extracted from.
///
/// Keyed the way [`super::MirOp`] keys a detected site: a CALL is its block's
/// terminator (one per block), a raw-deref STATEMENT is `(block, index)`. A
/// statement also carries the span the extractor gave it (the compiler's
/// `source_span_from_rustc_span` of `source_info.span`, which is byte-identical to
/// the extractor's `convert_span`), checked again at the site, so a statement
/// numbering that ever diverged between the two sides withholds nothing.
///
/// EMPTY IS FAIL-CLOSED: every detected site keeps its row.
#[derive(Debug, Clone, Default)]
pub struct SafetyDeclaredUnsafeOps {
    terminators: FxHashSet<BlockId>,
    statements: FxHashMap<(BlockId, usize), SourceSpan>,
}

impl SafetyDeclaredUnsafeOps {
    /// Declare `block`'s terminator.
    pub fn declare_terminator(&mut self, block: BlockId) {
        self.terminators.insert(block);
    }

    /// Declare statement `index` of `block`, whose extracted span is `span`.
    pub fn declare_statement(&mut self, block: BlockId, index: usize, span: SourceSpan) {
        self.statements.insert((block, index), span);
    }
}

/// The declared operations one generation actually WITHHELD a row for, as
/// [`with_safety_declared_unsafe_ops`] returns them. The compiler charges an
/// `assumption:safety-comment` row for every declared block that owns one of
/// them; an operation not in here kept whatever row it had.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SafetyDeclaredWithheld {
    /// Blocks whose terminator call kept no stand-in row.
    pub terminators: FxHashSet<BlockId>,
    /// `(block, statement index)` raw-reborrow sites that kept no
    /// `[unsafe:reborrow]` row. A raw-pointer READ is never in here: Trust models
    /// it, so one the engine did not interpret keeps its stand-in
    /// (`detection::decide_site`).
    pub statements: FxHashSet<(BlockId, usize)>,
}

/// One open scope (see [`with_safety_declared_unsafe_ops`]).
struct DeclaredScope {
    def_path: String,
    span: SourceSpan,
    declared: SafetyDeclaredUnsafeOps,
    withheld: SafetyDeclaredWithheld,
}

thread_local! {
    static DECLARED_SCOPES: RefCell<Vec<DeclaredScope>> = const { RefCell::new(Vec::new()) };
}

/// Run ONE generation of `func` with `declared` installed, and return its result
/// together with the operations it withheld. Only the innermost scope is read,
/// and only for the body it names (the same `def_path` AND the same function
/// span, so a twin body that renders the same path is not lent this one's
/// operations). The scope is closed on unwind too.
pub fn with_safety_declared_unsafe_ops<R>(
    func: &VerifiableFunction,
    declared: SafetyDeclaredUnsafeOps,
    f: impl FnOnce() -> R,
) -> (R, SafetyDeclaredWithheld) {
    struct Guard(usize);
    impl Drop for Guard {
        fn drop(&mut self) {
            let _ = DECLARED_SCOPES.try_with(|s| s.borrow_mut().truncate(self.0));
        }
    }
    let depth = DECLARED_SCOPES.with(|s| {
        let mut s = s.borrow_mut();
        s.push(DeclaredScope {
            def_path: func.def_path.clone(),
            span: func.span.clone(),
            declared,
            withheld: SafetyDeclaredWithheld::default(),
        });
        s.len() - 1
    });
    let guard = Guard(depth);
    let out = f();
    let withheld = DECLARED_SCOPES
        .with(|s| s.borrow_mut().get_mut(depth).map(|scope| std::mem::take(&mut scope.withheld)));
    drop(guard);
    (out, withheld.unwrap_or_default())
}

/// Whether the site `block` of `func` is a declared operation, RECORDING it as
/// withheld when it is. The caller mints nothing for a `true` answer and its
/// ordinary fail-closed row for a `false` one; nothing else may withhold a row on
/// this scope's authority.
pub(crate) fn withhold_declared_site(func: &VerifiableFunction, block: &UnsafeBlock) -> bool {
    DECLARED_SCOPES.with(|s| {
        let mut s = s.borrow_mut();
        let Some(scope) = s.last_mut() else { return false };
        if scope.def_path != func.def_path || scope.span != func.span {
            return false;
        }
        match block.origin {
            UnsafeOrigin::Call { .. } => {
                if !scope.declared.terminators.contains(&block.block_id) {
                    return false;
                }
                scope.withheld.terminators.insert(block.block_id);
            }
            UnsafeOrigin::RawDeref { stmt } => {
                if scope.declared.statements.get(&(block.block_id, stmt)) != Some(&block.span) {
                    return false;
                }
                scope.withheld.statements.insert((block.block_id, stmt));
            }
        }
        true
    })
}
