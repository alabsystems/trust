//! The independent Rust metadata half of the level-S owner binding.
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::DefId;
use trust_ir::{ParamId, Ty};

use super::{AuthenticatedTemplate, GenericSlot, OwnerBindings, Result, SlotKind, err};

pub fn owner_bindings(tcx: TyCtxt<'_>, owner: DefId) -> Result<OwnerBindings> {
    if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn) {
        return Err(err("template owner is not an ordinary function"));
    }
    let generics = tcx.generics_of(owner);
    let mut slots = Vec::with_capacity(generics.count());
    let mut compact = 0;
    if generics.count() > super::MAX_SLOTS {
        return Err(err("template owner slot budget"));
    }
    for i in 0..generics.count() {
        let p = generics.param_at(i, tcx);
        if p.index as usize != i {
            return Err(err("Rust generic parameter position mismatch"));
        }
        let kind = match p.kind {
            ty::GenericParamDefKind::Lifetime => SlotKind::Lifetime,
            ty::GenericParamDefKind::Type { .. } => {
                let p = ParamId::new(compact);
                compact += 1;
                SlotKind::Type(p)
            }
            ty::GenericParamDefKind::Const { .. } => {
                let source = tcx.type_of(p.def_id).instantiate_identity().skip_normalization();
                let pointer64 = tcx.data_layout.pointer_size().bits() == 64;
                let ty = match source.kind() {
                    ty::Bool => Ty::Bool,
                    ty::Char => Ty::Char,
                    ty::Int(ty::IntTy::I8) => Ty::I8,
                    ty::Int(ty::IntTy::I16) => Ty::I16,
                    ty::Int(ty::IntTy::I32) => Ty::I32,
                    ty::Int(ty::IntTy::I64) => Ty::I64,
                    ty::Int(ty::IntTy::I128) => Ty::I128,
                    ty::Int(ty::IntTy::Isize) if pointer64 => Ty::Isize,
                    ty::Uint(ty::UintTy::U8) => Ty::U8,
                    ty::Uint(ty::UintTy::U16) => Ty::U16,
                    ty::Uint(ty::UintTy::U32) => Ty::U32,
                    ty::Uint(ty::UintTy::U64) => Ty::U64,
                    ty::Uint(ty::UintTy::U128) => Ty::U128,
                    ty::Uint(ty::UintTy::Usize) if pointer64 => Ty::Usize,
                    _ => return Err(err("unsupported Rust template const-parameter type")),
                };
                let param = ParamId::new(compact);
                compact += 1;
                SlotKind::Const { param, ty }
            }
        };
        slots.push(GenericSlot {
            definition: crate::template_key::rustc::stable_def(tcx, p.def_id),
            kind,
        });
    }
    Ok(OwnerBindings { owner: crate::template_key::rustc::stable_def(tcx, owner), slots })
}

/// Validate the live capture's original/compact map against a fresh read of
/// Rust's complete generic metadata before a production encoder sees bytes.
pub fn check_capture(
    tcx: TyCtxt<'_>,
    owner: DefId,
    facts: &crate::template_lowering::LaneFacts,
) -> Result<OwnerBindings> {
    let bindings = owner_bindings(tcx, owner)?;
    if facts.owner != Some(bindings.owner) {
        return Err(err("template capture owner mismatch"));
    }
    let indices: Vec<_> = bindings
        .slots
        .iter()
        .enumerate()
        .filter_map(|(i, s)| (!matches!(s.kind, SlotKind::Lifetime)).then_some(i as u32))
        .collect();
    if facts.parameter_indices != indices {
        return Err(err("template capture positional map mismatch"));
    }
    if facts.params.len() != indices.len() {
        return Err(err("template capture compact parameter count mismatch"));
    }
    for (i, p) in facts.params.iter().enumerate() {
        match (p, &bindings.slots[indices[i] as usize].kind) {
            (crate::template_lowering::LaneParam::Type, SlotKind::Type(_)) => {}
            (crate::template_lowering::LaneParam::Const(a), SlotKind::Const { ty: b, .. })
                if a == b => {}
            _ => return Err(err("template capture slot kind/type mismatch")),
        }
    }
    Ok(bindings)
}

/// Production metadata input read. The Rust crate store independently supplies
/// the requested owner/slots. No MIR query, self-reported-owner decode, cache or
/// codegen token is involved in loading this level-S artifact.
pub fn load_upstream(tcx: TyCtxt<'_>, owner: DefId) -> Result<AuthenticatedTemplate> {
    if owner.is_local() {
        return Err(err("template metadata consumer requires an upstream definition"));
    }
    let expected = owner_bindings(tcx, owner)?;
    let header = tcx
        .trust_ir_crate_header(owner.krate)
        .ok_or_else(|| err("upstream crate has no Trust-IR producer header"))?;
    if header.trust_ir_version != trust_ir::binary::VERSION
        || header.entry_schema != crate::rmeta_entry::ENTRY_SCHEMA
    {
        return Err(err("upstream template crate schema/version mismatch"));
    }
    if let Some(refusal) = &header.crate_refusal {
        return Err(err(format!("upstream template crate refused: {refusal}")));
    }
    let blob = tcx.trust_ir_entry(owner).ok_or_else(|| {
        err(format!(
            "upstream template absent: {}",
            header.unencoded_reason(owner.index.as_u32()).unwrap_or("not in encode set")
        ))
    })?;
    super::read(&blob.0, &expected, tcx.sess.overflow_checks())
}
