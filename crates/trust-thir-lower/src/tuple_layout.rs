//! Transfer source-observed tuple layouts across module type relocation.
//!
//! Layout coherence is checked here; source refinement and codegen authority
//! remain separate requirements.

use trust_ir::{Module, Ty};

/// Copy only the type/layout context, without cloning instruction bodies.
pub(crate) fn context(module: &Module) -> Module {
    let mut out = Module::new("tuple_layout_context");
    out.target_info = module.target_info.clone();
    out.types = module.types.clone();
    out.structs = module.structs.clone();
    out.enums = module.enums.clone();
    out.records = module.records.clone();
    out.func_types = module.func_types.clone();
    out.closure_types = module.closure_types.clone();
    out.tuple_layouts = module.tuple_layouts.clone();
    out.closure_layouts = module.closure_layouts.clone();
    out
}

/// Preserve every source row after type relocation. All fallible work precedes
/// mutation of the destination layout table and target identity.
///
/// `remap` is the caller's ordinary type-relocation operation. A mapped tuple
/// must already exist in the destination type table. Identical observations
/// coalesce; conflicting observations refuse the merge regardless of order.
pub(crate) fn merge(
    source: &Module,
    destination: &mut Module,
    mut remap: impl FnMut(&Ty) -> Option<Ty>,
) -> Result<(), String> {
    source.validate_tuple_layouts().map_err(|e| format!("source tuple layout: {e}"))?;
    destination.validate_tuple_layouts().map_err(|e| format!("destination tuple layout: {e}"))?;
    if source.tuple_layouts.is_empty() {
        return Ok(());
    }
    let source_target = source.target_info.as_ref().ok_or("source tuple layout has no target")?;
    if destination.target_info.as_ref().is_some_and(|t| t != source_target) {
        return Err("tuple layout target mismatch".into());
    }
    let mut candidate = context(destination);
    candidate.target_info = Some(source_target.clone());
    for descriptor in &source.tuple_layouts {
        let source_ty = source
            .types
            .get(descriptor.tuple_type.as_usize())
            .ok_or("tuple layout type is absent")?;
        let mapped = remap(source_ty).ok_or("tuple layout type could not be remapped")?;
        if !matches!(mapped, Ty::Tuple(_)) {
            return Err("tuple layout remap is not a tuple".into());
        }
        let id = candidate
            .types
            .iter()
            .position(|t| *t == mapped)
            .ok_or("remapped tuple layout type was not interned")?;
        let mut relocated = descriptor.clone();
        relocated.tuple_type = trust_ir::TyId::new(
            u32::try_from(id).map_err(|_| "tuple layout type index exceeds u32")?,
        );
        if let Some(existing) = candidate
            .tuple_layout_descriptor(&mapped)
            .map_err(|e| format!("tuple layout lookup: {e}"))?
        {
            if existing.size != relocated.size
                || existing.align != relocated.align
                || existing.field_offsets != relocated.field_offsets
            {
                return Err("conflicting tuple layout observations".into());
            }
        } else {
            candidate.tuple_layouts.push(relocated);
        }
    }
    candidate.validate_tuple_layouts().map_err(|e| format!("remapped tuple layout: {e}"))?;
    destination.target_info = candidate.target_info;
    destination.tuple_layouts = candidate.tuple_layouts;
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_ir::{Endianness, TargetInfo, TupleLayoutDescriptor, TyId};

    use super::*;

    fn fixture() -> Module {
        let mut m = Module::new("source");
        m.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        let ty = m
            .add_type(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]))
            .expect("Module::add_type: test fixture");
        m.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: ty,
            size: 16,
            align: 8,
            field_offsets: vec![8, 0, 9],
        });
        m
    }

    #[test]
    fn relocates_and_coalesces_identical_layouts() {
        let src = fixture();
        let mut dst = Module::new("destination");
        dst.add_type(Ty::Bool).expect("Module::add_type: test fixture");
        dst.add_type(src.types[0].clone()).expect("Module::add_type: test fixture");
        merge(&src, &mut dst, |t| Some(t.clone())).unwrap();
        assert_eq!(dst.tuple_layouts[0].tuple_type, TyId::new(1));
        assert_eq!(dst.tuple_layouts[0].field_offsets, vec![8, 0, 9]);
        assert_eq!(dst.target_info, src.target_info);
        let before = dst.clone();
        merge(&src, &mut dst, |t| Some(t.clone())).unwrap();
        assert_eq!(dst, before);
    }

    #[test]
    fn uses_the_callers_nested_type_remap() {
        let mut src = fixture();
        src.types = vec![Ty::U16, Ty::Tuple(vec![Ty::Array(TyId::new(0), 2), Ty::U8])];
        src.tuple_layouts = vec![TupleLayoutDescriptor {
            tuple_type: TyId::new(1),
            size: 6,
            align: 2,
            field_offsets: vec![0, 4],
        }];
        let mut dst = Module::new("destination");
        dst.types = vec![Ty::Bool, Ty::U16, Ty::Tuple(vec![Ty::Array(TyId::new(1), 2), Ty::U8])];
        merge(&src, &mut dst, |t| match t {
            Ty::Tuple(_) => Some(dst_tuple()),
            _ => None,
        })
        .unwrap();
        assert_eq!(dst.tuple_layouts[0].tuple_type, TyId::new(2));
        assert_eq!(dst.ty_layout_shape(&dst_tuple()).unwrap().size_bytes(), Some(6));
    }
    fn dst_tuple() -> Ty {
        Ty::Tuple(vec![Ty::Array(TyId::new(1), 2), Ty::U8])
    }

    #[test]
    fn conflicts_are_refused_in_both_orders_without_mutation() {
        let a = fixture();
        let mut b = a.clone();
        b.tuple_layouts[0].field_offsets.swap(0, 2);
        for (src, mut dst) in [(&a, b.clone()), (&b, a.clone())] {
            let before = dst.clone();
            assert!(merge(src, &mut dst, |t| Some(t.clone())).unwrap_err().contains("conflicting"));
            assert_eq!(dst, before);
        }
    }

    #[test]
    fn target_mismatch_and_missing_mapping_leave_destination_unchanged() {
        let src = fixture();
        let mut dst = src.clone();
        dst.target_info.as_mut().unwrap().endianness = Endianness::Big;
        let before = dst.clone();
        assert!(merge(&src, &mut dst, |t| Some(t.clone())).is_err());
        assert_eq!(dst, before);
        dst = Module::new("unbound");
        let before = dst.clone();
        assert!(merge(&src, &mut dst, |_| None).is_err());
        assert_eq!(dst, before);
        assert!(merge(&src, &mut dst, |t| Some(t.clone())).is_err());
        assert_eq!(dst, before);
    }

    #[test]
    fn malformed_unused_source_and_destination_rows_are_rejected() {
        let good = fixture();
        let mut bad = good.clone();
        bad.tuple_layouts[0].field_offsets[2] = 8;
        for (src, mut dst) in [(&bad, good.clone()), (&good, bad.clone())] {
            let before = dst.clone();
            assert!(merge(src, &mut dst, |t| Some(t.clone())).is_err());
            assert_eq!(dst, before);
        }
    }

    #[test]
    fn context_preserves_declared_closure_byte_images() {
        let mut source = fixture();
        let func = source
            .add_func_type(trust_ir::FuncTy {
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        let closure = source
            .add_closure_type(trust_ir::ClosureTy {
                func,
                captures: vec![Ty::U8, Ty::U64],
            })
            .unwrap();
        source.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure,
            size: 16,
            align: 8,
            capture_offsets: vec![8, 0],
        });
        source.validate_closure_layouts().unwrap();
        let expected = source.ty_layout_shape(&Ty::Closure(closure)).unwrap();

        let copied = context(&source);
        assert_eq!(copied.closure_layouts, source.closure_layouts);
        assert_eq!(copied.ty_layout_shape(&Ty::Closure(closure)).unwrap(), expected);
        assert_eq!(copied.tuple_layouts, source.tuple_layouts);
    }
}
