//! Trust: compiler-only provenance query for a single local bang-macro item.
//! Shared verbatim with real compiler callback regressions; no typed decoder.

use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;
use rustc_span::hygiene::{ExpnKind, MacroKind};

pub(super) struct Origin {
    pub function_path: String,
    pub function_def_path_hash: [u64; 2],
    pub macro_path: String,
    pub macro_def_path_hash: [u64; 2],
    pub definition_span: Span,
    pub invocation_span: Span,
    pub definition_text: String,
    pub invocation_text: String,
}

pub(super) fn capture(tcx: TyCtxt<'_>, owner: LocalDefId) -> Option<Origin> {
    if tcx.def_kind(owner) != DefKind::Fn || tcx.def_kind(tcx.local_parent(owner)) != DefKind::Mod {
        return None;
    }
    let item_span = tcx.source_span(owner);
    if item_span.is_dummy() || !item_span.from_expansion() {
        return None;
    }
    let expansion_id = item_span.ctxt().outer_expn();
    let expansion = expansion_id.expn_data();
    if !matches!(expansion.kind, ExpnKind::Macro(MacroKind::Bang, _))
        || expansion.parent != rustc_span::hygiene::ExpnId::root()
    {
        return None;
    }
    let macro_owner = expansion.macro_def_id?.as_local()?;
    let rustc_hir::Node::Item(macro_item) = tcx.hir_node_by_def_id(macro_owner) else {
        return None;
    };
    let rustc_hir::ItemKind::Macro(_, definition, _) = macro_item.kind else {
        return None;
    };
    if !definition.macro_rules
        || definition.eii_declaration.is_some()
        || rustc_attr_ir::find_attr!(tcx, macro_owner, RustcBuiltinMacro { .. })
    {
        return None;
    }
    // HIR's macro item span and the expansion's call site are the original
    // parser-owned full item/invocation extents, not identifier/token spans.
    let definition_span = macro_item.span;
    let invocation_span = expansion.call_site;
    let ordinary = |span: rustc_span::Span| !span.is_dummy() && !span.from_expansion();
    if !ordinary(definition_span) || !ordinary(invocation_span) {
        return None;
    }
    let nodes = tcx.opt_hir_owner_nodes(owner)?;
    if nodes.nodes.len() > 65_536 {
        return None;
    }
    for (local_id, _) in nodes.nodes.iter_enumerated() {
        let span = tcx
            .hir_span(rustc_hir::HirId { owner: rustc_hir::OwnerId { def_id: owner }, local_id });
        if span.is_dummy() {
            return None;
        }
        // Reject nested expansion/desugaring, including an imported/proc macro
        // in the body. Substituted ordinary tokens must come from the full
        // invocation or local definition we are binding here.
        if span.from_expansion() {
            if span.ctxt().outer_expn() != expansion_id {
                return None;
            }
        } else if !definition_span.contains(span) && !invocation_span.contains(span) {
            return None;
        }
    }
    let text = |span: Span| {
        // Availability bound, not verifier or proof-budget credit.
        if (span.hi() - span.lo()).0 as usize > 1024 * 1024 {
            return None;
        }
        let text = tcx.sess.source_map().span_to_snippet(span).ok()?;
        (!text.is_empty()).then_some(text)
    };
    Some(Origin {
        function_path: trust_mir_extract::safe_def_path_str(tcx, owner.to_def_id()),
        function_def_path_hash: stable_path(tcx, owner),
        macro_path: trust_mir_extract::safe_def_path_str(tcx, macro_owner.to_def_id()),
        macro_def_path_hash: stable_path(tcx, macro_owner),
        definition_span,
        invocation_span,
        definition_text: text(definition_span)?,
        invocation_text: text(invocation_span)?,
    })
}

fn stable_path(tcx: TyCtxt<'_>, owner: LocalDefId) -> [u64; 2] {
    let hash = tcx.def_path_hash(owner.to_def_id());
    [hash.stable_crate_id().as_u64(), hash.local_hash().as_u64()]
}
