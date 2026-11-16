//! Trust (D4 increment A, 2026-09-24): the per-def SOURCE FACT "this body, or a
//! body it owns, contains user `unsafe` source" — the LOCAL provider of the
//! `trust_def_has_user_unsafe_source` query.
//!
//! # Why a source fact has to cross the crate boundary
//!
//! A downstream compilation that RE-DERIVES a dependency body's verdict from the
//! dependency's encoded MIR (`trust_verify/foreign_rederivation.rs`) sees only
//! that MIR. Some unsafe constructs leave no trace there: InstSimplify erases a
//! lifetime-only `transmute::<&'a T, &'static T>` to a plain copy, and the HIR
//! half that charges it for a LOCAL body (`validity_transmute.rs`,
//! `hir_transmute_call_sites`) has no HIR to read for a foreign one. Measured on
//! the stage-1 snapshot at `4e9fe36bf`: a declared verify-off dependency
//! `pub fn extend(r: &u32) -> u32 { let s: &'static u32 = unsafe {
//! transmute(r) }; *s }` called from a verifying binary built rc=0 (one
//! tolerated runtime-checked row), while the byte-identical LOCAL copy was
//! refused. So a foreign body cleared a weaker bar than the same local body.
//!
//! Rust guarantees safe source is UB-free, and every unsafe operation in
//! compiling code sits lexically in an `unsafe fn`, an `unsafe { }` block, or an
//! `unsafe impl`. A body whose source has none of those needs no unsafe-row
//! reasoning at all; a body that has one is the only kind whose encoded MIR can
//! be missing an unsafe hazard. The OWNING crate's compiler has the HIR, so it
//! computes the fact and writes it into its metadata beside the MIR
//! (`rustc_metadata` table `trust_no_user_unsafe_source`). A consumer that finds
//! the fact TRUE — or finds no row at all — declines to re-derive the body.
//!
//! # What counts (every answer errs toward `true`)
//!
//! Computed for the TYPECK ROOT, so a closure, inline const or coroutine body
//! answers with its enclosing item (a closure inside an `unsafe fn` inherits the
//! unsafe context), and the walk covers EVERY nested body and nested item of the
//! root (`nested_filter::All`): closures, inline consts, anon consts, and items
//! declared inside the body. `true` when any of:
//!
//! * the root is an `unsafe fn` (its body is an unsafe context), or `#[naked]`;
//! * the root is an associated item of an `unsafe impl`;
//! * any walked block is a USER-PROVIDED `unsafe { }` block
//!   (`UnsafeSource::UserProvided` — the `format_args!` desugaring's
//!   compiler-generated `unsafe { Arguments::new(..) }` wrapper is a
//!   foundational-TCB construction, the same carve-out
//!   `def_uses_user_unsafe_source` makes for the std-print tolerance);
//! * the root has no walkable HIR body (a Clean-origin def, a constructor, a
//!   foreign item): there is nothing to confirm, so it is not confirmed safe.
//!
//! # What this is and is not
//!
//! A SOURCE FACT, not a verdict. It says nothing about whether the body is
//! correct, panic-free or verified, and nothing that reads it ever grants
//! credit: its only consumer DECLINES a body when it is `true`. It is trusted
//! exactly as the encoded MIR it travels beside is trusted (the P-MIR premise,
//! `docs/TCB.md`): the producer is a Trust compiler whose version string the
//! consumer checked (E0514), and a missing row answers `true`.
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::hir::nested_filter;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

/// The local provider of `trust_def_has_user_unsafe_source`. See the module
/// docs; `true` is the fail-closed answer.
pub(crate) fn trust_def_has_user_unsafe_source(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    let root = tcx.typeck_root_def_id_local(def);
    if root != def {
        // Closures, inline consts and synthetic coroutine bodies answer with
        // their enclosing item, whose walk covers them (and is cached).
        return tcx.trust_def_has_user_unsafe_source(root.to_def_id());
    }
    // A Clean-origin def has no HIR body (walking it `span_bug!`s on the
    // synthetic owner). Its emission cannot spell `unsafe`, but nothing here
    // needs to credit it, so it answers the fail-closed `true`.
    if crate::clean_origin_mir::is_clean_origin(tcx, root) {
        return true;
    }
    let def_kind = tcx.def_kind(root);
    // Only a HIR body owner has a body to walk; every other def (a constructor,
    // a synthesized associated type, a foreign item, …) is answered without
    // touching HIR, and fail-closed.
    if !matches!(
        def_kind,
        DefKind::Fn
            | DefKind::AssocFn
            | DefKind::Const { .. }
            | DefKind::AssocConst { .. }
            | DefKind::Static { .. }
            | DefKind::AnonConst
    ) {
        return true;
    }
    if matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
        if tcx.fn_sig(root).instantiate_identity().skip_binder().safety().is_unsafe() {
            return true;
        }
        if tcx.codegen_fn_attrs(root).flags.contains(CodegenFnAttrFlags::NAKED) {
            return true;
        }
    }
    if matches!(def_kind, DefKind::AssocFn | DefKind::AssocConst { .. })
        && let Some(impl_def_id) = tcx.trait_impl_of_assoc(root.to_def_id())
        && tcx.impl_trait_header(impl_def_id).safety.is_unsafe()
    {
        return true;
    }
    let Some(body) = tcx.hir_maybe_body_owned_by(root) else {
        return true;
    };
    let mut finder = UserUnsafeBlockFinder { tcx, found: false };
    finder.visit_body(body);
    finder.found
}

struct UserUnsafeBlockFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    found: bool,
}

impl<'tcx> Visitor<'tcx> for UserUnsafeBlockFinder<'tcx> {
    // Every nested body (closures, inline and anon consts) AND every nested item
    // (an `fn`/`const` declared inside the body): an `unsafe` anywhere under the
    // root counts against the root.
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if self.found {
            return;
        }
        intravisit::walk_expr(self, expr);
    }

    fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) {
        if self.found {
            return;
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) {
        if self.found {
            return;
        }
        if let hir::BlockCheckMode::UnsafeBlock(hir::UnsafeSource::UserProvided) = block.rules {
            self.found = true;
            return;
        }
        intravisit::walk_block(self, block);
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if self.found {
            return;
        }
        // A nested `unsafe fn` or `unsafe impl` counts by its signature, as the
        // root does; its body is walked below either way.
        // (`FnHeader::is_unsafe` also answers `true` for a safe
        // `#[target_feature]` fn, which the type system treats as unsafe to
        // call; erring toward `true` is the fail-closed direction.)
        match &item.kind {
            hir::ItemKind::Fn { sig, .. } if sig.header.is_unsafe() => self.found = true,
            hir::ItemKind::Impl(hir::Impl { of_trait: Some(of_trait), .. })
                if of_trait.safety.is_unsafe() =>
            {
                self.found = true
            }
            _ => {}
        }
        if !self.found {
            intravisit::walk_item(self, item);
        }
    }

    fn visit_impl_item(&mut self, item: &'tcx hir::ImplItem<'tcx>) {
        if self.found {
            return;
        }
        if let hir::ImplItemKind::Fn(sig, _) = &item.kind
            && sig.header.is_unsafe()
        {
            self.found = true;
            return;
        }
        intravisit::walk_impl_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'tcx hir::TraitItem<'tcx>) {
        if self.found {
            return;
        }
        if let hir::TraitItemKind::Fn(sig, _) = &item.kind
            && sig.header.is_unsafe()
        {
            self.found = true;
            return;
        }
        intravisit::walk_trait_item(self, item);
    }
}
