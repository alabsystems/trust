//! Typed generic callable transport. This level-S path never enters runtime
//! assembly and never manufactures a callee body. The consumer still owes the
//! exact source-semantic adapter/body at the instantiated declared signature.

use rustc_middle::ty;
use rustc_span::def_id::DefId;
use trust_ir::template::TemplateArg;
use trust_ir::{FuncId, FuncTy, Inst, ValueId};

use super::{CalleeHole, LaneParam};

impl<'a, 'tcx> crate::LowerCx<'a, 'tcx> {
    pub(crate) fn admit_template_callee(
        &mut self,
        item: DefId,
        args: ty::GenericArgs<'tcx>,
    ) -> Result<FuncId, &'static str> {
        if self.tcx.intrinsic(item).is_some() {
            return Err("Call(template intrinsic has no ordinary callee body)");
        }
        let lane = self.template.as_ref().ok_or("Call(template lane absent)")?;
        let owner = crate::template_key::rustc::stable_def(self.tcx, self.body_def);
        if lane.owner != Some(owner) {
            return Err("Call(template key owner mismatch)");
        }
        let key = crate::template_key::rustc::checked_call_key(self.tcx, item, args, self.body_def)
            .map_err(|_| "Call(template callee identity)")?;
        if let Some(hole) = lane.callee_holes.iter().find(|h| h.key == key) {
            return Ok(hole.decl);
        }
        let env = lane.typing_env;
        let declared = self.tcx.fn_sig(item).instantiate(self.tcx, args);
        let declared = crate::producer_try_normalize(self.tcx, env, declared)
            .map_err(|_| "Call(template declared signature normalization)")?
            .skip_normalization();
        if declared.bound_vars().iter().any(|v| !matches!(v, ty::BoundVariableKind::Region(_))) {
            return Err("Call(template bound signature)");
        }
        let declared = self.tcx.instantiate_bound_regions_with_erased(declared);
        let builtin_call = self.tcx.def_kind(item) == rustc_hir::def::DefKind::AssocFn
            && self
                .tcx
                .trait_of_assoc(item)
                .and_then(|tr| self.tcx.fn_trait_kind_from_def_id(tr))
                .is_some();
        if self
            .tcx
            .codegen_fn_attrs(item)
            .flags
            .contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::TRACK_CALLER)
        {
            return Err("Call(template caller location)");
        }
        if declared.c_variadic()
            || declared.fn_sig_kind.splatted().is_some()
            || !matches!(declared.abi(), rustc_abi::ExternAbi::Rust)
                && !(declared.abi() == rustc_abi::ExternAbi::RustCall && builtin_call)
        {
            return Err("Call(template callable convention)");
        }
        let mark = self.unsupported.len();
        let params = declared.inputs().iter().map(|t| self.map_ty(*t)).collect();
        let ret = self.map_ty(declared.output());
        if self.unsupported.len() != mark {
            return Err("Call(template declared signature type)");
        }
        let signature = FuncTy {
            params,
            returns: if declared.output().is_unit() || declared.output().is_never() {
                vec![]
            } else {
                vec![ret]
            },
            is_vararg: false,
            abi: None,
        };
        let lane = self.template.as_ref().unwrap();
        let mut dependencies = Vec::new();
        for index in
            crate::template_key::parameters(&key).map_err(|_| "Call(template key dependencies)")?
        {
            let p = *lane.index_map.get(&index).ok_or("Call(template missing parameter)")?;
            let argument = match &lane.params[p.as_usize()].1 {
                LaneParam::Type => {
                    TemplateArg::Type(trust_ir::TyG::Ext(trust_ir::TemplateRef::Param(p)))
                }
                LaneParam::Const(ty) => TemplateArg::Const {
                    value: trust_ir::ConstantG::Ext(trust_ir::TemplateRef::Param(p)),
                    ty: ty.clone(),
                },
            };
            dependencies.push((index, argument));
        }
        if dependencies.is_empty() {
            return Err("Call(template ground callee)");
        }
        let next = self.callees.len() + 1;
        if next >= crate::ADAPTER_FUNC_ID_BASE as usize {
            return Err("Call(template FuncId space exhausted)");
        }
        let id = FuncId::new(next as u32);
        let path = rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(item));
        self.callees.push(crate::CalleeRef {
            func_id: id,
            is_local: item.is_local(),
            def_index: item.index.as_u32(),
            def_id: item,
            definition: crate::lineage::DefinitionIdentity::from_def_id(self.tcx, item),
            concrete_key: None,
            instance_args: None,
            def_path: path,
            force_havoc: false,
            site_def_id: item,
            site_args: None,
            ret_ty: signature.returns.first().cloned(),
            ret_ty_conflict: false,
            abi: crate::calling_convention::FunctionAbi::declared(self.tcx, declared.abi(), declared.c_variadic()),
            params: crate::ParamSignature::Signed(signature.params.clone()),
        });
        let lane = self.template.as_mut().unwrap();
        let hole_id = trust_ir::HoleId::new((lane.callee_holes.len() + lane.type_holes.len()) as u32);
        lane.callee_holes.push(CalleeHole {
            id: hole_id,
            decl: id,
            key,
            signature,
            dependencies,
        });
        Ok(id)
    }

    /// Evaluate every original operand exactly once, in source order. In
    /// particular a FnOnce call retains its by-value receiver and argument tuple.
    pub(crate) fn emit_template_callable(
        &mut self,
        callee: FuncId,
        args: &[rustc_middle::thir::ExprId],
        result: ty::Ty<'tcx>,
        span: rustc_span::Span,
    ) -> Option<ValueId> {
        let signature = self
            .template
            .as_ref()?
            .callee_holes
            .iter()
            .find(|h| h.decl == callee)?
            .signature
            .clone();
        if args.len() != signature.params.len() {
            self.unsupported.push((format!("{span:?}"), "Call(template argument count)"));
            return None;
        }
        let mut values = Vec::with_capacity(args.len());
        for (&expr, expected) in args.iter().zip(&signature.params) {
            if self.map_ty(self.thir.exprs[expr].ty) != *expected {
                self.unsupported.push((format!("{span:?}"), "Call(template argument type)"));
                return None;
            }
            values.push(self.lower_expr(expr)?);
        }
        let mapped = self.map_ty(result);
        let returns = if result.is_unit() || result.is_never() { vec![] } else { vec![mapped] };
        if returns != signature.returns {
            self.unsupported.push((format!("{span:?}"), "Call(template result type)"));
            return None;
        }
        self.emit_call_at(span, Inst::Call { callee, args: values }, result)
    }
}
