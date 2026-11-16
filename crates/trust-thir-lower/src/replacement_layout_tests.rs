//! Helper-level contract for the immutable table shared by a replacement check.
//! Native prepass tests separately cover Rust layouts, admissions and refusals.

use trust_ir::ty::{FieldDef, StructDef, StructRepr, Ty};
use trust_ir::value::{StructId, TyId};
use trust_ir::{Endianness, Module, TargetInfo};

fn target(pointer_size: u32) -> Module {
    let mut module = Module::new("replacement_layout_table");
    module.target_info = Some(TargetInfo {
        triple: if pointer_size == 4 { "wasm32-unknown-unknown" } else { "aarch64-apple-darwin" }
            .into(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    module
}

fn structure(id: u32, fields: Vec<Ty>, pointer_size: u32) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        size: Some(u64::from(pointer_size) * fields.len() as u64),
        align: Some(u64::from(pointer_size)),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(index, ty)| FieldDef {
                name: format!("f{index}"),
                ty,
                offset: Some(u64::from(pointer_size) * index as u64),
            })
            .collect(),
        repr: StructRepr::C,
        origin: None,
    }
}

fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

fn chain(depth: u32, pointer_size: u32) -> Module {
    let mut module = target(pointer_size);
    module.add_struct(structure(0, vec![Ty::Ptr], pointer_size));
    for id in 1..depth {
        module.add_struct(structure(id, vec![s(id - 1)], pointer_size));
    }
    module
}

#[test]
fn replacement_layout_shared_table_preserves_errors_and_target_width() {
    for pointer_size in [4, 8] {
        let mut module = chain(4, pointer_size);
        // Two entry points to the same cycle, a tail into it, a missing row,
        // and an incoherent declared size must keep their exact errors.
        module.add_struct(structure(4, vec![s(5)], pointer_size));
        module.add_struct(structure(5, vec![s(4)], pointer_size));
        module.add_struct(structure(6, vec![s(4)], pointer_size));
        module.add_struct(structure(7, vec![s(999)], pointer_size));
        let mut incoherent = structure(8, vec![Ty::Ptr], pointer_size);
        incoherent.size = Some(0);
        module.add_struct(incoherent);
        let mut queries = vec![Ty::Ptr, Ty::Usize, Ty::Array(TyId::new(999), 1)];
        queries.extend((0..=8).map(s));
        let expected: Vec<_> = queries.iter().map(|ty| module.ty_layout_shape(ty)).collect();
        assert!(expected.iter().any(Result::is_ok));
        assert!(expected.iter().filter(|row| row.is_err()).count() >= 6);
        assert_eq!(expected[0].as_ref().unwrap().size_bits, u64::from(pointer_size) * 8);
        assert_eq!(expected[1].as_ref().unwrap().size_bits, u64::from(pointer_size) * 8);
        let forward: Vec<_> = (0..queries.len()).collect();
        let backward: Vec<_> = forward.iter().copied().rev().collect();
        let errors_first: Vec<_> = forward
            .iter()
            .copied()
            .filter(|&i| expected[i].is_err())
            .chain(forward.iter().copied().filter(|&i| expected[i].is_ok()))
            .collect();
        for order in [&forward, &backward, &errors_first] {
            let layouts = module.layout_table();
            for round in 0..3 {
                for &index in order {
                    let actual = layouts.ty_layout(&queries[index]).map(|shape| (*shape).clone());
                    assert_eq!(
                        actual, expected[index],
                        "pointer_size={pointer_size}, round={round}, query={index}"
                    );
                }
            }
        }
        // i686's noncanonical scalar ABI and unknown targets both keep their
        // fail-closed behavior, including repeated cached refusals.
        for triple in ["i686-unknown-linux-gnu", "unknown-scalar-layout-target"] {
            module.target_info.as_mut().unwrap().triple = triple.into();
            let layouts = module.layout_table();
            for _ in 0..3 {
                for ty in [Ty::Usize, Ty::Ptr, s(3)] {
                    let expected = module.ty_layout_shape(&ty);
                    let actual = layouts.ty_layout(&ty).map(|shape| (*shape).clone());
                    assert_eq!(actual, expected);
                }
            }
            assert!(layouts.ty_layout(&Ty::Usize).is_err());
        }
    }
}

#[test]
fn replacement_layout_shared_table_visits_each_nested_row_once() {
    // The old per-component call builds a fresh table for each suffix. Count
    // actual library work, independently of elapsed time and compiler mapping.
    for depth in [8, 32, 128] {
        let module = chain(depth, 8);
        let layouts = module.layout_table();
        let mut fresh_nodes = 0;
        let mut fresh_steps = 0;
        for id in (0..depth).rev() {
            let fresh = module.layout_table();
            let expected = fresh.ty_layout_shape(&s(id)).unwrap();
            let actual = layouts.ty_layout(&s(id)).unwrap();
            assert_eq!(*actual, expected);
            fresh_nodes += fresh.stats().nodes;
            fresh_steps += fresh.stats().steps;
        }
        let first = layouts.stats();
        assert_eq!(fresh_nodes, (depth * (depth + 1) / 2) as usize);
        assert_eq!(first.nodes, depth as usize);
        assert!(first.steps <= u64::from(depth) * 8);
        for id in 0..depth {
            layouts.ty_layout(&s(id)).unwrap();
        }
        assert_eq!(layouts.stats().nodes, first.nodes);
        eprintln!(
            "replacement layout depth={depth} fresh_nodes={fresh_nodes} shared_nodes={} fresh_steps={fresh_steps} shared_steps={}",
            first.nodes, first.steps
        );
    }
}
