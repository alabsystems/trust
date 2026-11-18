// Copyright 2026 Andrew Yates. SPDX-License-Identifier: MIT OR Apache-2.0
//! Exact-source lowering MODEL for core's total thin-pointer `eq` body `a == b`.
//! Diagnostic identity alone is insufficient: require the real loaded sysroot,
//! exact selected source fingerprints, concrete input/signature and pinned target.
//! Correspondence to that Rust body remains an explicit frontend/model premise;
//! this creates no body-admission capability, CIC axiom or proof license.

use rustc_span::def_id::{CRATE_DEF_INDEX, DefId};

use super::*;

// Source fingerprints of Root's immutable2887 library. Qualification must
// observe these on the ACTUAL loaded core metadata, never substitute a path.
const PTR_SOURCE: &str = "md5=73ae7ad8a6be7f881d1ccc94630d1845";
const ROOT_SOURCE: &str = "md5=b112b10649c938ea9442a344829d8f73";

pub(super) struct CoreThinPtrEqV1<'tcx> {
    input: RustcTy<'tcx>,
}
impl<'tcx> CoreThinPtrEqV1<'tcx> {
    pub(super) fn input(&self) -> RustcTy<'tcx> {
        self.input
    }
}

pub(super) fn recognize<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Option<CoreThinPtrEqV1<'tcx>> {
    let core = tcx.lang_items().sized_trait()?.krate;
    if def.is_local()
        || def.krate != core
        || tcx.crate_name(core).as_str() != "core"
        || !trust_mir_extract::is_real_sysroot_crate(tcx, core)
        || !tcx.is_diagnostic_item(rustc_span::Symbol::intern("ptr_eq"), def)
        || tcx.def_kind(def) != rustc_hir::def::DefKind::Fn
        || args.len() != 1
        || args.has_non_region_param()
        || args.has_non_region_infer()
        || u32::from(tcx.sess.target.pointer_width) != PINNED_POINTER_BITS
    {
        return None;
    }
    let signature = tcx.fn_sig(def).instantiate(tcx, args).skip_normalization().skip_binder();
    let [left, right] = signature.inputs() else { return None };
    let ty::RawPtr(pointee, rustc_hir::Mutability::Not) = *left.kind() else { return None };
    if left != right
        || args[0].as_type() != Some(pointee)
        || pointee.has_aliases()
        || !is_sized_unrevealed(tcx, pointee, ty::TypingEnv::fully_monomorphized())
        || signature.output() != tcx.types.bool
        || signature.c_variadic()
        || signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
    {
        return None;
    }
    let source_matches = |owner: DefId, expected: &str| {
        let span = tcx.def_span(owner);
        if span.is_dummy() {
            return false;
        }
        let file = tcx.sess.source_map().lookup_source_file(span.lo());
        file.cnum == core && file.src_hash.to_string() == expected
    };
    let root = DefId { krate: core, index: CRATE_DEF_INDEX };
    if !source_matches(def, PTR_SOURCE) || !source_matches(root, ROOT_SOURCE) {
        return None;
    }
    Some(CoreThinPtrEqV1 { input: *left })
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    pub(super) fn try_lower_core_thin_ptr_eq(
        &mut self,
        span: rustc_span::Span,
        output: RustcTy<'tcx>,
        fun: ExprId,
        args: &[ExprId],
    ) -> Option<Option<ValueId>> {
        let ty::FnDef(def, generic_args) = *self.monomorphize(self.thir.exprs[fun].ty).kind()
        else {
            return None;
        };
        let comparison = recognize(self.tcx, def, generic_args.skip_binder())?;
        if args.len() != 2
            || self.monomorphize(output) != self.tcx.types.bool
            || args
                .iter()
                .any(|id| self.monomorphize(self.thir.exprs[*id].ty) != comparison.input())
        {
            self.unsupported.push((format!("{span:?}"), "Call(core thin ptr_eq signature)"));
            return Some(None);
        }
        // The common Call arm has evaluated the actual callee effects already.
        // These are the original source arguments, once each, left before right.
        let Some(lhs) = self.lower_expr(args[0]) else { return Some(None) };
        let Some(rhs) = self.lower_expr(args[1]) else { return Some(None) };
        let result = self.fresh();
        self.push_node(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::Ptr, lhs, rhs })
                .with_result(result),
        );
        Some(Some(result))
    }
}
