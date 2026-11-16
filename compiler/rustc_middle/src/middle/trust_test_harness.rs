// Trust: CB4 (2026-09-28) — identify the items rustc's libtest harness
// SYNTHESIZES, by where they came from.
//
//! Under `--test`, rustc generates code the author never wrote:
//!
//! * per `#[test]`/`#[bench]`, the builtin expander
//!   (`rustc_builtin_macros::test::expand_test_or_bench`) emits a
//!   `#[rustc_test_marker] const NAME: test::TestDescAndFn` descriptor whose
//!   `testfn` field holds a runner closure
//!   (`|| test::assert_test_result(NAME())`, or `|b| …(NAME(b))` for a bench);
//! * the harness pass (`rustc_builtin_macros::test_harness::mk_main`) emits
//!   `#[rustc_main] fn main() { test::test_main_static(&[..]) }`.
//!
//! The Trust verification gate and the `-Ztrust-ir-lower=strict` coverage
//! check both need to tell those items apart from user code. Before CB4 the
//! only test was "the typeck root carries `#[rustc_test_marker]`", and that is
//! FORGEABLE (MEASURED): the attribute is an ordinary (feature-gated) attribute
//! a user can write, and `#[test_case]` pushes it onto the user's OWN fn, const
//! or static. So this module keys on PROVENANCE instead — on the expansion that
//! produced the item's own span — and never on a name or on the attribute alone:
//!
//! * `ExpnKind::AstPass(AstPass::TestHarness)` is minted only by the harness
//!   pass itself (`expansion_for_ast_pass`, after all macro expansion), so no
//!   user macro can emit a span that carries it;
//! * the builtin `#[test]`/`#[bench]` expansion is recognized by the macro
//!   DEFINITION it resolved to — one carrying `#[rustc_builtin_macro]` whose
//!   builtin name is `test`/`bench` — exactly the rule the resolver uses to hand
//!   out the compiler's own expander (`rustc_expand::base` /
//!   `rustc_resolve::macros`). A user attribute macro that merely resolves under
//!   the NAME `test` produces `ExpnKind::Macro(Attr, test)` too, but its
//!   definition is not a builtin, so it is not matched. The builtin expander
//!   gives every item it mints `with_def_site_ctxt` spans (root context plus its
//!   own mark), so the identification survives `macro_rules!` and proc-macro
//!   wrappers around the `#[test]`.
//!
//! The user's own `#[test]` function keeps the user's context and is never
//! returned here: it is user code and stays in every lane.

// Upstream 1.101: the `find_attr!` macro lives in `rustc_attr_ir`.
use rustc_attr_ir::find_attr;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_span::hygiene::{AstPass, ExpnData, ExpnKind, MacroKind};
use rustc_span::sym;

use crate::ty::TyCtxt;

/// Trust (CB4): an item rustc's libtest harness synthesized.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TestHarnessItem {
    /// The harness entry point `main` (`test::test_main_static[_abort]`, or a
    /// `#![test_runner]` call under `custom_test_frameworks`).
    HarnessMain,
    /// The `TestDescAndFn` descriptor const a builtin `#[test]`/`#[bench]` emits.
    TestDescriptorConst,
    /// The runner closure inside that descriptor.
    TestRunnerClosure,
}

impl TestHarnessItem {
    /// Stable machine tag.
    pub const fn tag(self) -> &'static str {
        match self {
            Self::HarnessMain => "harness-main",
            Self::TestDescriptorConst => "test-descriptor-const",
            Self::TestRunnerClosure => "test-runner-closure",
        }
    }
}

/// Trust (CB4): which libtest-harness item `def` is, if rustc synthesized it.
///
/// `None` outside a `--test` compilation and for every item the author wrote —
/// including the author's own `#[test]` fn, a `#[test_case]` item, and a
/// hand-written `#[rustc_test_marker]` const or its closure.
pub fn test_harness_synthesized_item(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<TestHarnessItem> {
    if !tcx.sess.is_test_crate() {
        return None;
    }
    let own = tcx.source_span(def).ctxt().outer_expn_data();
    match tcx.def_kind(def) {
        DefKind::Fn
            if own.kind == ExpnKind::AstPass(AstPass::TestHarness)
                && find_attr!(tcx, def, RustcMain) =>
        {
            Some(TestHarnessItem::HarnessMain)
        }
        // Upstream 1.101: the expander emits the descriptor as a `static`
        // (`cx.item_static`); before, it was a `const`. Provenance is the same
        // either way — the builtin expansion plus the marker — so both item
        // kinds are the descriptor.
        DefKind::Const { .. } | DefKind::Static { .. }
            if is_builtin_test_expansion(tcx, &own)
                && find_attr!(tcx, def, RustcTestMarker(..)) =>
        {
            Some(TestHarnessItem::TestDescriptorConst)
        }
        DefKind::Closure => {
            let parent = tcx.local_parent(def);
            let from_the_same_expansion = tcx.source_span(parent).ctxt().outer_expn()
                == tcx.source_span(def).ctxt().outer_expn();
            (from_the_same_expansion
                && is_builtin_test_expansion(tcx, &own)
                && test_harness_synthesized_item(tcx, parent)
                    == Some(TestHarnessItem::TestDescriptorConst))
            .then_some(TestHarnessItem::TestRunnerClosure)
        }
        _ => None,
    }
}

/// Trust (CB4): the macro definition that the expansion which produced `def`'s
/// own span resolved to, if any.
pub fn own_expansion_macro_def(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<DefId> {
    tcx.source_span(def).ctxt().outer_expn_data().macro_def_id
}

/// Trust (CB4): whether `def`'s own span was produced by the compiler's builtin
/// `#[test]`/`#[bench]` expansion. False for the author's own test function,
/// which the expander re-emits with the author's context.
pub fn is_from_builtin_test_expansion(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    is_builtin_test_expansion(tcx, &tcx.source_span(def).ctxt().outer_expn_data())
}

/// Trust (CB4): whether `data` is an expansion of the COMPILER's builtin
/// `#[test]` or `#[bench]` attribute — identified by the macro definition it
/// resolved to, never by the name it was invoked under.
pub fn is_builtin_test_expansion(tcx: TyCtxt<'_>, data: &ExpnData) -> bool {
    matches!(data.kind, ExpnKind::Macro(MacroKind::Attr, _))
        && data.macro_def_id.is_some_and(|macro_def| is_builtin_test_macro(tcx, macro_def))
}

fn is_builtin_test_macro(tcx: TyCtxt<'_>, macro_def: DefId) -> bool {
    find_attr!(tcx, macro_def, RustcBuiltinMacro { builtin_name, .. } => *builtin_name)
        .map(|builtin_name| builtin_name.unwrap_or_else(|| tcx.item_name(macro_def)))
        .is_some_and(|name| name == sym::test || name == sym::bench)
}

/// Trust (CB4): whether every item in this crate that carries
/// `#[rustc_test_marker]` is a descriptor the builtin `#[test]`/`#[bench]`
/// synthesized.
///
/// The harness `main` runs EVERY marked item. With `custom_test_frameworks`, a
/// `#[test_case]` const the author wrote (a `TestDescAndFn` whose `testfn` is
/// any function pointer) is run by a `main` whose MIR is byte-for-byte the
/// builtin shape (MEASURED). So excluding `main` is sound only when this holds;
/// otherwise `main` executes user-chosen code and stays verified.
pub fn test_harness_markers_are_all_builtin(tcx: TyCtxt<'_>) -> bool {
    tcx.hir_crate_items(()).owners().all(|owner| {
        !find_attr!(tcx, owner.def_id, RustcTestMarker(..))
            || test_harness_synthesized_item(tcx, owner.def_id)
                == Some(TestHarnessItem::TestDescriptorConst)
    })
}
