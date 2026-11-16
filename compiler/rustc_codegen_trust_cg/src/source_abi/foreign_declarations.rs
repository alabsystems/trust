//! Original same-session foreign Items bound to exact immutable declarations.
use std::collections::BTreeSet;
use std::sync::Arc;
use rustc_middle::ty::TyCtxt;
use trust_ir::{FuncId, Module};

pub(crate) fn check(tcx: TyCtxt<'_>, module: &Arc<Module>) -> Result<BTreeSet<FuncId>, String> {
    tcx.sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
        |handoff| {
            let mut checked = BTreeSet::new();
            for function in module.functions.iter().filter(|f| f.is_declaration()) {
                if !crate::trust_ir_frontend::native_source_module::foreign_declarations::recorded(module, function.id) {
                    return Err(format!("foreign declaration `{}` has no supported exact scalar prototype", function.name));
                }
                let original = handoff.declaration(function.id)
                    .ok_or("foreign declaration has no exact retained source identity")?;
                if !Arc::ptr_eq(original.module(), module)
                    || original.function() != function
                    || module.func_type(function.ty) != Some(original.signature())
                {
                    return Err("foreign declaration belongs to another source image".into());
                }
                let instance = original.foreign_instance(tcx)?;
                if !tcx.is_foreign_item(instance.def_id())
                    || tcx.symbol_name(instance).name != function.name
                {
                    return Err("foreign declaration differs from its original Item or link symbol".into());
                }
                checked.insert(function.id);
            }
            Ok(checked)
        },
    )
}
