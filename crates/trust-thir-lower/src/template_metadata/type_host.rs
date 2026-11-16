//! Canonical placement of actual producer type images into unlicensed S data.
//! Roots travel through one ordinary signature row so the existing exhaustive
//! module merger remaps every nested type. There is no parallel type walker,
//! nominal-name lookup, body constructor, admission token or proof authority.

use trust_ir::{BodyGate, FuncTy, Module, Ty};

use crate::concrete_type_transport::ConcreteTypes;

/// The resulting partial construction and its roots share one table context.
/// Full module validation remains the instantiator's final postcondition: its
/// pre-existing generic placeholders are not complete level-R types yet.
pub struct MergedTypes {
    module: Module,
    roots: Vec<Ty>,
}
impl MergedTypes {
    pub fn module(&self) -> &Module { &self.module }
    pub fn roots(&self) -> &[Ty] { &self.roots }
    pub(crate) fn into_parts(self) -> (Module, Vec<Ty>) { (self.module, self.roots) }
}

pub fn merge(host: &Module, source: &ConcreteTypes<'_>) -> Result<MergedTypes, String> {
    merge_image(host, source.module(), source.roots())
}

fn merge_image(host: &Module, source: &Module, roots: &[Ty]) -> Result<MergedTypes, String> {
    if host.target_info != source.target_info || host.target_info.is_none() {
        return Err("template type image target differs from its construction".into());
    }
    if host.completeness.is_some()
        || host.functions.iter().any(|f| matches!(f.body_gate, Some(BodyGate::Gated { .. })))
    {
        return Err("template type placement cannot modify a licensed/completeness image".into());
    }
    if !source.functions.is_empty() || !source.func_types.is_empty()
        || !source.globals.is_empty() || !source.records.is_empty()
        || !source.closure_types.is_empty() || !source.closure_layouts.is_empty()
        || !source.drop_glue.is_empty() || !source.proof_obligations.is_empty()
        || !source.proof_certificates.is_empty() || !source.obligation_diagnostics.is_empty()
        || !source.spec_modules.is_empty() || !source.imports.is_empty()
        || !source.predicates.is_empty() || !source.universes.is_empty()
        || !source.files.is_empty() || !source.global_asm.is_empty()
        || source.completeness.is_some()
    {
        return Err("template type image carries unsupported non-type state".into());
    }
    let mut incoming = source.clone();
    let carrier = incoming.intern_func_type(FuncTy {
        params: roots.to_vec(), returns: Vec::new(), is_vararg: false, abi: None,
    }).map_err(|e| format!("template root carrier refused: {e}"))?;
    let errors = trust_ir_build::validate::validate_module(&incoming);
    if !errors.is_empty() {
        return Err(format!("template source type image invalid: {errors:?}"));
    }
    let mut out = host.clone();
    let remap = trust_ir_build::merge::merge_into(
        &mut out, &incoming, &trust_ir_build::merge::MergePolicy::VERIFICATION_IMAGE,
    ).map_err(|e| format!("template canonical type merge refused: {e}"))?;
    let carrier = remap.func_ty(carrier).ok_or("template root carrier has no canonical remap")?;
    let signature = out.func_type(carrier).ok_or("template remapped root carrier is absent")?;
    if signature.params.len() != roots.len() || !signature.returns.is_empty()
        || signature.is_vararg || signature.abi.is_some()
    {
        return Err("template root carrier changed shape during canonical merge".into());
    }
    let roots = signature.params.clone();
    // The canonical merger is the only remapper. Independently enforce the
    // host's append-only boundary, including future Module fields by whole Eq.
    macro_rules! preserve {
        ($($table:ident),+ $(,)?) => {{
            let mut unchanged = out.clone();
            $(if out.$table.len() < host.$table.len()
                || out.$table[..host.$table.len()] != host.$table {
                return Err(concat!("template type merge changed existing ", stringify!($table)).into());
            }
            unchanged.$table = host.$table.clone();)+
            if &unchanged != host {
                return Err("template type merge changed non-type construction state".into());
            }
        }};
    }
    preserve!(types, structs, enums, tuple_layouts, func_types);
    Ok(MergedTypes { module: out, roots })
}

#[cfg(test)]
mod tests;
