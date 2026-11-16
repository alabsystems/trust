// Copyright 2026 Andrew Yates. SPDX-License-Identifier: MIT OR Apache-2.0
//! Versioned lowering MODEL for the real core u64 wrapper. Loader residency,
//! exact instantiated types and metadata source fingerprints identify the
//! selected implementation. They do not prove its Rust body. Correspondence of
//! that implementation to wrapping integer addition remains a frontend/model
//! premise, never a CIC axiom, body admission or source-refinement capability.

use super::*;
use rustc_span::def_id::{DefId, CRATE_DEF_INDEX};
use rustc_span::Span;

pub(super) const MODEL: &str = "core-u64-wrapping-add-v1";
// These are the source fingerprints carried by the actual loaded compiler
// metadata, not guessed filesystem paths or source-spellable attributes. The
// source SHA256 readset and actual core artifact are bound by qualification.
const UINT_SOURCE: &str = "md5=1083ddf946cfa87f80b15f81ad75960a";
const NUM_SOURCE: &str = "md5=f38f64651974e5815ef831c2f75bfa2a";
const ROOT_SOURCE: &str = "md5=b112b10649c938ea9442a344829d8f73";
const INTRINSIC_SOURCE: &str = "md5=76cc4e39fbf3376b25f24a051a6b0ce7";

pub(super) struct CoreU64WrappingAddV1(());

fn source_matches(tcx: TyCtxt<'_>, span: Span, owner: rustc_span::def_id::CrateNum, hash: &str) -> bool {
    if span.is_dummy() {
        return false;
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    file.cnum == owner && file.src_hash.to_string() == hash
}

pub(super) fn recognize<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Option<CoreU64WrappingAddV1> {
    let core = tcx.lang_items().sized_trait()?.krate;
    if def.is_local()
        || def.krate != core
        || tcx.crate_name(core).as_str() != "core"
        // This existing helper only reads metadata/loader residency; no MIR is queried.
        || !trust_mir_extract::is_real_sysroot_crate(tcx, core)
        || !tcx.opt_item_name(def).is_some_and(|n| n.as_str() == "wrapping_add")
        || !args.is_empty()
        || tcx.trait_of_assoc(def).is_some()
    {
        return None;
    }
    let implementation = tcx.inherent_impl_of_assoc(def)?;
    if implementation.krate != core
        || tcx.type_of(implementation).instantiate_identity().skip_normalization() != tcx.types.u64
    {
        return None;
    }
    let signature = tcx.fn_sig(def).instantiate(tcx, args).skip_normalization().skip_binder();
    if signature.inputs() != [tcx.types.u64, tcx.types.u64]
        || signature.output() != tcx.types.u64
        || signature.c_variadic()
        || signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
    {
        return None;
    }
    let root = DefId { krate: core, index: CRATE_DEF_INDEX };
    if !source_matches(tcx, tcx.def_span(def), core, UINT_SOURCE)
        || !source_matches(tcx, tcx.def_span(def).source_callsite(), core, NUM_SOURCE)
        || !source_matches(tcx, tcx.def_span(implementation), core, NUM_SOURCE)
        || !source_matches(tcx, tcx.def_span(root), core, ROOT_SOURCE)
    {
        return None;
    }
    let intrinsics = tcx.module_children(root).iter()
        .find(|child| child.ident.name.as_str() == "intrinsics")?.res.opt_def_id()?;
    if intrinsics.krate != core {
        return None;
    }
    let intrinsic = tcx.module_children(intrinsics).iter()
        .find(|child| child.ident.name.as_str() == "wrapping_add")?.res.opt_def_id()?;
    if intrinsic.krate != core
        || !tcx.intrinsic(intrinsic).is_some_and(|item|
            item.name.as_str() == "wrapping_add" && item.must_be_overridden)
        || !source_matches(tcx, tcx.def_span(intrinsic), core, INTRINSIC_SOURCE)
    {
        return None;
    }
    Some(CoreU64WrappingAddV1(()))
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    pub(super) fn try_lower_core_u64_wrapping_add(
        &mut self,
        span: Span,
        output: RustcTy<'tcx>,
        fun: ExprId,
        args: &[ExprId],
    ) -> Option<Option<ValueId>> {
        let ty::FnDef(def, generic_args) = *self.monomorphize(self.thir.exprs[fun].ty).kind() else {
            return None;
        };
        let _model = recognize(self.tcx, def, generic_args.skip_binder())?;
        if args.len() != 2
            || self.monomorphize(output) != self.tcx.types.u64
            || args.iter().any(|id| self.monomorphize(self.thir.exprs[*id].ty) != self.tcx.types.u64)
        {
            self.unsupported.push((format!("{span:?}"), "Call(core wrapping_add signature)"));
            return Some(None);
        }
        // Callee effects were already evaluated by the common Call arm. Both
        // actual arguments are evaluated exactly once and in source order.
        let Some(lhs) = self.lower_expr(args[0]) else { return Some(None) };
        let Some(rhs) = self.lower_expr(args[1]) else { return Some(None) };
        let result = self.fresh();
        self.push_node(InstrNode::new(Inst::BinOp {
            op: BinOp::Add, ty: Ty::U64, lhs, rhs,
        }).with_result(result));
        Some(Some(result))
    }
}
