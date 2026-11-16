//! Preserve source-observed closure frames across per-body type relocation.

use trust_ir::{ClosureLayoutDescriptor, ClosureTy, ClosureTyId, Module};

fn same_image(a: &ClosureLayoutDescriptor, b: &ClosureLayoutDescriptor) -> bool {
    a.origin == b.origin
        && a.size == b.size
        && a.align == b.align
        && a.capture_offsets == b.capture_offsets
}

/// A body's pending frame observations remain visible until `merge` installs
/// them. Otherwise a newly interned known frame looks indistinguishable from
/// an unobserved frame while subsequent logical twins are interned.
#[derive(Default)]
pub(crate) struct Interner<'a> {
    pending: Vec<(ClosureTyId, Option<&'a ClosureLayoutDescriptor>)>,
}

impl<'a> Interner<'a> {
    /// Logical capture types alone do not identify a physical environment.
    /// Keep different frames and missing observations distinct, including
    /// observations made earlier in this same body. The caller validates both
    /// contexts before interning and transfers the frames through `merge`.
    pub(crate) fn intern(
        &mut self,
        module: &mut Module,
        ty: ClosureTy,
        source_layout: Option<&'a ClosureLayoutDescriptor>,
    ) -> Result<ClosureTyId, trust_ir::IdSpaceExhausted> {
        for (index, existing) in module.closure_types.iter().enumerate() {
            if *existing != ty {
                continue;
            }
            let id = ClosureTyId::new(index as u32);
            let destination_layout = match self.pending.iter().find(|(pending, _)| *pending == id) {
                Some((_, layout)) => *layout,
                None => module.closure_layouts.iter().find(|row| row.closure == id),
            };
            let equivalent = match (source_layout, destination_layout) {
                (None, None) => true,
                (Some(a), Some(b)) => same_image(a, b),
                _ => false,
            };
            if equivalent {
                return Ok(id);
            }
        }
        let id = module.add_closure_type(ty)?;
        self.pending.push((id, source_layout));
        Ok(id)
    }
}

/// Relocate every descriptor or leave the destination's layout rows and target
/// untouched. Both modules' unused descriptors are checked as well.
pub(crate) fn merge(
    source: &Module,
    destination: &mut Module,
    remap: &[ClosureTyId],
) -> Result<(), String> {
    source.validate_closure_layouts().map_err(|e| format!("source closure layout: {e}"))?;
    destination
        .validate_closure_layouts()
        .map_err(|e| format!("destination closure layout: {e}"))?;
    if source.closure_layouts.is_empty() {
        return Ok(());
    }
    let target = source.target_info.as_ref().ok_or("source closure layout has no target")?;
    if destination.target_info.as_ref().is_some_and(|other| other != target) {
        return Err("closure layout target mismatch".into());
    }
    let mut candidate = crate::tuple_layout::context(destination);
    candidate.target_info = Some(target.clone());
    for row in &source.closure_layouts {
        let id = *remap.get(row.closure.as_usize()).ok_or("closure layout has no type mapping")?;
        if candidate.closure_type(id).is_none() {
            return Err("closure layout maps to an absent type".into());
        }
        if let Some(previous) = candidate
            .closure_layout_descriptor(id)
            .map_err(|e| format!("closure layout lookup: {e}"))?
        {
            if !same_image(previous, row) {
                return Err("conflicting closure layout observations".into());
            }
        } else {
            let mut relocated = row.clone();
            relocated.closure = id;
            candidate.closure_layouts.push(relocated);
        }
    }
    candidate.validate_closure_layouts().map_err(|e| format!("remapped closure layout: {e}"))?;
    destination.target_info = candidate.target_info;
    destination.closure_layouts = candidate.closure_layouts;
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_ir::{Endianness, FuncTy, TargetInfo, Ty};

    use super::*;

    fn fixture(offsets: [u64; 2]) -> Module {
        let mut module = Module::new("closure_layout_source");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        let func = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        let closure =
            module.add_closure_type(ClosureTy { func, captures: vec![Ty::U64, Ty::U64] }).unwrap();
        module.closure_layouts.push(ClosureLayoutDescriptor {
            origin: None,
            closure,
            size: 16,
            align: 8,
            capture_offsets: offsets.into(),
        });
        module.validate_closure_layouts().unwrap();
        module
    }

    #[test]
    fn logical_twins_with_different_physical_images_keep_distinct_ids() {
        let mut interner = Interner::default();
        let mut destination = fixture([0, 8]);
        let source = fixture([8, 0]);
        let first = ClosureTyId::new(0);
        let second = interner
            .intern(
                &mut destination,
                source.closure_types[0].clone(),
                Some(&source.closure_layouts[0]),
            )
            .unwrap();
        assert_ne!(first, second);
        merge(&source, &mut destination, &[second]).unwrap();
        assert_eq!(
            destination.closure_layout_descriptor(first).unwrap().unwrap().capture_offsets,
            vec![0, 8]
        );
        assert_eq!(
            destination.closure_layout_descriptor(second).unwrap().unwrap().capture_offsets,
            vec![8, 0]
        );
        assert_eq!(
            interner
                .intern(
                    &mut destination,
                    source.closure_types[0].clone(),
                    Some(&source.closure_layouts[0])
                )
                .unwrap(),
            second
        );
    }

    fn nominal_origin(key: u8) -> trust_ir::ty::TypeOrigin {
        trust_ir::ty::TypeOrigin::Rust {
            stable_crate_id: 7,
            def_path_hash: [key; 16],
            args_digest: trust_ir::ProofDigest::zero(),
        }
    }

    #[test]
    fn identical_frames_keep_distinct_known_and_unknown_origins() {
        for (source_origin, destination_origin) in [
            (Some(nominal_origin(1)), Some(nominal_origin(2))),
            (Some(nominal_origin(1)), None),
            (None, Some(nominal_origin(1))),
        ] {
            let mut source = fixture([0, 8]);
            source.closure_layouts[0].origin = source_origin.clone();
            let mut destination = fixture([0, 8]);
            destination.closure_layouts[0].origin = destination_origin;
            let mut interner = Interner::default();
            let relocated = interner
                .intern(
                    &mut destination,
                    source.closure_types[0].clone(),
                    Some(&source.closure_layouts[0]),
                )
                .unwrap();
            assert_ne!(relocated, ClosureTyId::new(0));
            merge(&source, &mut destination, &[relocated]).unwrap();
            assert_eq!(destination.closure_layouts[1].origin, source_origin);
            assert_eq!(
                interner
                    .intern(
                        &mut destination,
                        source.closure_types[0].clone(),
                        Some(&source.closure_layouts[0]),
                    )
                    .unwrap(),
                relocated,
            );
        }
    }

    #[test]
    fn conflicting_nominal_origin_refuses_without_changing_destination() {
        let mut source = fixture([0, 8]);
        source.closure_layouts[0].origin = Some(nominal_origin(1));
        let mut destination = fixture([0, 8]);
        destination.closure_layouts[0].origin = Some(nominal_origin(2));
        let before = destination.clone();
        assert!(merge(&source, &mut destination, &[ClosureTyId::new(0)]).is_err());
        assert_eq!(destination, before);
    }

    #[test]
    fn absent_source_evidence_does_not_inherit_a_known_frame() {
        let mut interner = Interner::default();
        let mut destination = fixture([0, 8]);
        let ty = destination.closure_types[0].clone();
        let missing = interner.intern(&mut destination, ty.clone(), None).unwrap();
        assert_ne!(missing, ClosureTyId::new(0));
        assert!(destination.closure_layout_descriptor(missing).unwrap().is_none());
        assert_eq!(interner.intern(&mut destination, ty, None).unwrap(), missing);
    }

    #[test]
    fn same_body_known_and_unobserved_twins_remain_distinct_in_both_orders() {
        for known_first in [true, false] {
            let mut source = fixture([0, 8]);
            source.add_closure_type(source.closure_types[0].clone()).unwrap();
            let known = usize::from(!known_first);
            source.closure_layouts[0].closure = ClosureTyId::new(known as u32);
            source.validate_closure_layouts().unwrap();
            let mut destination = source.clone();
            destination.closure_types.clear();
            destination.closure_layouts.clear();
            let mut ids = Vec::new();
            let mut interner = Interner::default();
            for (index, ty) in source.closure_types.iter().enumerate() {
                ids.push(
                    interner
                        .intern(
                            &mut destination,
                            ty.clone(),
                            source
                                .closure_layouts
                                .iter()
                                .find(|row| row.closure.as_usize() == index),
                        )
                        .unwrap(),
                );
            }
            assert_ne!(ids[0], ids[1], "known-first={known_first}");
            merge(&source, &mut destination, &ids).unwrap();
            assert!(destination.closure_layout_descriptor(ids[known]).unwrap().is_some());
            assert!(destination.closure_layout_descriptor(ids[1 - known]).unwrap().is_none());
        }
    }

    #[test]
    fn same_body_known_frames_coalesce_only_when_their_images_match() {
        for offsets in [[0, 8], [8, 0]] {
            let mut source = fixture([0, 8]);
            source.add_closure_type(source.closure_types[0].clone()).unwrap();
            source.closure_layouts.push(ClosureLayoutDescriptor {
                origin: None,
                closure: ClosureTyId::new(1),
                size: 16,
                align: 8,
                capture_offsets: offsets.into(),
            });
            source.validate_closure_layouts().unwrap();
            let mut destination = source.clone();
            destination.closure_types.clear();
            destination.closure_layouts.clear();
            let mut interner = Interner::default();
            let mut ids = Vec::new();
            for (index, ty) in source.closure_types.iter().enumerate() {
                ids.push(
                    interner
                        .intern(&mut destination, ty.clone(), Some(&source.closure_layouts[index]))
                        .unwrap(),
                );
            }
            assert_eq!(ids[0] == ids[1], offsets == [0, 8]);
            merge(&source, &mut destination, &ids).unwrap();
            destination.validate_closure_layouts().unwrap();
        }
    }

    #[test]
    fn relocates_and_coalesces_identical_frames() {
        let source = fixture([8, 0]);
        let mut destination = fixture([0, 8]);
        let id = destination.add_closure_type(source.closure_types[0].clone()).unwrap();
        merge(&source, &mut destination, &[id]).unwrap();
        assert_eq!(destination.closure_layouts[1].closure, id);
        assert_eq!(destination.ty_layout_shape(&Ty::Closure(id)).unwrap().size_bytes(), Some(16));
        let before = destination.clone();
        merge(&source, &mut destination, &[id]).unwrap();
        assert_eq!(destination, before);
    }

    #[test]
    fn conflicting_frames_refuse_both_orders_without_mutation() {
        let a = fixture([0, 8]);
        let b = fixture([8, 0]);
        for (source, mut destination) in [(&a, b.clone()), (&b, a.clone())] {
            let before = destination.clone();
            assert!(
                merge(source, &mut destination, &[ClosureTyId::new(0)])
                    .unwrap_err()
                    .contains("conflicting")
            );
            assert_eq!(destination, before);
        }
    }

    #[test]
    fn missing_mapping_and_target_mismatch_leave_destination_unchanged() {
        let source = fixture([0, 8]);
        for ids in [vec![], vec![ClosureTyId::new(9)]] {
            let mut destination = source.clone();
            let before = destination.clone();
            assert!(merge(&source, &mut destination, &ids).is_err());
            assert_eq!(destination, before);
        }
        let mut destination = source.clone();
        destination.target_info.as_mut().unwrap().endianness = Endianness::Big;
        let before = destination.clone();
        assert!(merge(&source, &mut destination, &[ClosureTyId::new(0)]).is_err());
        assert_eq!(destination, before);
    }

    #[test]
    fn every_unused_or_duplicate_descriptor_is_checked() {
        let good = fixture([0, 8]);
        let mut bad = good.clone();
        bad.closure_layouts.push(bad.closure_layouts[0].clone());
        for (source, mut destination) in [(&bad, good.clone()), (&good, bad.clone())] {
            let before = destination.clone();
            assert!(merge(source, &mut destination, &[ClosureTyId::new(0)]).is_err());
            assert_eq!(destination, before);
        }
        bad = good.clone();
        bad.closure_layouts[0].capture_offsets[1] = 0;
        let mut destination = good.clone();
        assert!(merge(&bad, &mut destination, &[ClosureTyId::new(0)]).is_err());
        assert_eq!(destination, good);
    }
}
