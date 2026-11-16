use trust_types::{
    AdtAuth, AdtKind, AdtLayoutInfo, FnSig, LayoutTarget, LocalDecl, TupleLayoutInfo, TupleLayouts,
    VerifiableBody,
};

use super::*;

fn marker(name: &str) -> Ty {
    Ty::Datatype { name: name.into(), variants: vec![] }
}

fn structure(name: &str, fields: Vec<Ty>) -> Ty {
    let count = fields.len();
    let mut ty =
        Ty::adt(name, fields.into_iter().enumerate().map(|(i, ty)| (i.to_string(), ty)).collect());
    if let Ty::Adt { adt_kind, layout, .. } = &mut ty {
        *adt_kind = Some(AdtKind::Struct);
        *layout = Some(Box::new(AdtLayoutInfo {
            size: count as u64 * 8,
            align: 8,
            field_offsets: (0..count as u64).map(|i| i * 8).collect(),
            repr: "c".into(),
        }));
    }
    ty
}

fn parity(defs: &DatatypeDefs, inputs: &[Ty]) {
    for reverse in [false, true] {
        let mut cached = Normalizer::new(defs);
        for round in 0..3 {
            for index in 0..inputs.len() {
                let index = if reverse { inputs.len() - index - 1 } else { index };
                let input = &inputs[index];
                let before = input.clone();
                assert_eq!(
                    cached.normalize(input),
                    super::super::normalize(input, defs),
                    "request {index}, repetition {round}, reverse={reverse}"
                );
                assert_eq!(*input, before, "normalization mutated the source Ty");
            }
        }
    }
}

#[test]
fn complete_requests_hit_and_keep_transient_authority_and_private_copies() {
    let stamp = Some(AdtAuth::TotalDrop(None));
    let owned = Ty::Seq { elem: Box::new(Ty::u64()), drop_auth: stamp };
    let mut definition =
        structure("Value", vec![Ty::Ref { mutable: false, inner: Box::new(owned) }]);
    if let Ty::Adt { arbitrary_precision, .. } = &mut definition {
        *arbitrary_precision = stamp;
    }
    let defs = [("Value".into(), definition.clone())].into();
    let mut cached = Normalizer::new(&defs);
    let input = marker("Value");
    let mut first = cached.normalize(&input);
    assert_eq!(first, definition);
    assert_eq!(cached.entries.len(), 1);
    assert_eq!(cached.misses, 1);
    // Mutating a caller's returned tree must not alter the retained value.
    if let Ty::Adt { fields, arbitrary_precision, .. } = &mut first {
        *arbitrary_precision = None;
        fields.make_mut()[0].1 = Ty::Bool;
    }
    let second = cached.normalize(&input);
    assert_eq!(second, definition);
    assert_ne!(second, first);
    assert_eq!(cached.misses, 1, "a complete repeated root should not expand again");
    let Ty::Adt { arbitrary_precision, fields, .. } = second else { panic!("physical definition") };
    assert_eq!(arbitrary_precision, stamp);
    let Ty::Ref { inner, .. } = &fields[0].1 else { panic!("reference field") };
    let Ty::Seq { drop_auth, .. } = inner.as_ref() else { panic!("owned pointee") };
    assert_eq!(*drop_auth, stamp);
    assert_eq!(defs["Value"], definition, "original authority/evidence is unchanged");
}

#[test]
fn same_names_in_distinct_contexts_keep_full_table_and_authority_identity() {
    let mut authenticated = structure("Value", vec![Ty::u64()]);
    if let Ty::Adt { arbitrary_precision, .. } = &mut authenticated {
        *arbitrary_precision = Some(AdtAuth::TotalDrop(None));
    }
    let plain = structure("Value", vec![Ty::u64()]);
    let different = structure("Value", vec![Ty::Bool]);
    assert_ne!(authenticated, plain, "transient stamp is part of exact Ty equality");
    for definition in [authenticated, plain, different] {
        let defs = [("Value".into(), definition)].into();
        parity(&defs, &[marker("Value"), marker("Missing")]);
    }
    parity(&DatatypeDefs::new(), &[marker("Value")]);
}

#[test]
fn negative_results_cycles_dst_and_exhaustion_match_the_uncached_algorithm() {
    let mut malformed = structure("Malformed", vec![Ty::u64()]);
    if let Ty::Adt { layout: Some(layout), .. } = &mut malformed {
        layout.align = 0;
    }
    let defs = [
        ("Physical".into(), structure("Physical", vec![Ty::u64()])),
        ("Malformed".into(), malformed),
        (
            "Logical".into(),
            Ty::Datatype { name: "Logical".into(), variants: vec![("Mk".into(), vec![])] },
        ),
        ("Miskeyed".into(), structure("Another", vec![Ty::u64()])),
        ("Cycle".into(), structure("Cycle", vec![marker("Cycle")])),
        ("Dst".into(), structure("Dst", vec![Ty::Str])),
        (
            "PointerDst".into(),
            structure(
                "PointerDst",
                vec![Ty::Ref { mutable: false, inner: Box::new(marker("Dst")) }],
            ),
        ),
        ("Huge".into(), structure("Huge", vec![Ty::u64(); super::super::MAX_NODES])),
        ("A".into(), structure("A", vec![Ty::u64(); 6000])),
        ("B".into(), structure("B", vec![Ty::u64(); 5000])),
        ("Small".into(), structure("Small", vec![Ty::u64(); 200])),
    ]
    .into();
    let names = ["Missing", "Malformed", "Logical", "Miskeyed", "Cycle", "PointerDst", "Huge"];
    let mut cached = Normalizer::new(&defs);
    for name in names {
        let input = marker(name);
        assert_eq!(cached.normalize(&input), input);
        let misses = cached.misses;
        assert_eq!(cached.normalize(&input), super::super::normalize(&input, &defs));
        assert_eq!(cached.misses, misses, "unchanged complete result should be retained: {name}");
    }
    let siblings = Ty::Tuple(vec![marker("A"), marker("B")]);
    // These individual results exceed the retention cap. Preserve the original
    // uncached sibling-exhaustion case without calling it warm-cache coverage.
    cached.normalize(&marker("A"));
    cached.normalize(&marker("B"));
    assert!(!cached.entries.iter().any(|entry| matches!(entry.name.as_ref(), "A" | "B")));
    assert_eq!(cached.normalize(&siblings), siblings);
    parity(&defs, &[siblings, marker("Physical")]);

    let mut warm = Normalizer::new(&defs);
    let small = marker("Small");
    let expanded = super::super::normalize(&small, &defs);
    assert_ne!(expanded, small, "the standalone request must expand successfully");
    assert_eq!(warm.normalize(&small), expanded);
    assert!(
        warm.entries.iter().any(|entry| entry.name.as_ref() == "Small" && entry.result == expanded),
        "the complete expanded result must actually be retained"
    );
    let misses = warm.misses;
    assert_eq!(warm.normalize(&small), expanded);
    assert_eq!(warm.misses, misses, "the repeated standalone request must actually hit");
    // 128 occurrences of 200 leaves exceed the original shared 16,384-node
    // budget even without counting eligibility work. A retained standalone
    // result cannot shortcut recursive work or rescue an exhausted prefix.
    let repeated = Ty::Tuple(vec![small; 128]);
    let uncached = super::super::normalize(&repeated, &defs);
    assert_eq!(uncached, repeated, "the original core must roll back the entire tuple");
    assert_eq!(warm.normalize(&repeated), uncached);
    assert_eq!(warm.misses, misses + 1, "the combined root still executes the bounded core");

    let mut deep = Ty::u64();
    for _ in 0..super::super::MAX_DEPTH {
        deep = Ty::Array { elem: Box::new(deep), len: 1 };
    }
    let deep_defs = [("Deep".into(), structure("Deep", vec![deep]))].into();
    parity(&deep_defs, &[marker("Deep")]);
}

#[test]
fn key_entry_and_retained_byte_limits_only_bypass_caching() {
    let long_name = "L".repeat(MAX_KEY_BYTES + 1);
    let mut defs = DatatypeDefs::new();
    defs.insert(long_name.clone(), structure(&long_name, vec![Ty::u64()]));
    for index in 0..=MAX_ENTRIES {
        let name = format!("Value{index}");
        defs.insert(name.clone(), structure(&name, vec![Ty::u64()]));
    }
    let mut oversized_key = Normalizer::new(&defs);
    for _ in 0..2 {
        let input = marker(&long_name);
        assert_eq!(oversized_key.normalize(&input), super::super::normalize(&input, &defs));
    }
    assert!(oversized_key.entries.is_empty(), "an oversized key alone must bypass caching");
    assert_eq!(oversized_key.misses, 2);
    let mut cached = Normalizer::new(&defs);
    for index in 0..=MAX_ENTRIES {
        let input = marker(&format!("Value{index}"));
        assert_eq!(cached.normalize(&input), super::super::normalize(&input, &defs));
    }
    assert_eq!(cached.entries.len(), MAX_ENTRIES);
    let misses = cached.misses;
    for input in [marker(&format!("Value{MAX_ENTRIES}")), marker(&long_name)] {
        for _ in 0..2 {
            assert_eq!(cached.normalize(&input), super::super::normalize(&input, &defs));
        }
    }
    assert_eq!(cached.misses, misses + 4);
    let mut wide = structure("Wide", vec![Ty::u64()]);
    if let Ty::Adt { fields, .. } = &mut wide {
        fields.make_mut()[0].0 = "x".repeat(MAX_RETAINED_BYTES);
    }
    let defs =
        [("Wide".into(), wide), ("Small".into(), structure("Small", vec![Ty::u64()]))].into();
    let mut cached = Normalizer::new(&defs);
    for _ in 0..2 {
        assert_eq!(
            cached.normalize(&marker("Wide")),
            super::super::normalize(&marker("Wide"), &defs)
        );
    }
    assert!(cached.entries.is_empty(), "oversized result cannot be retained");
    assert_eq!(cached.misses, 2);
    assert_eq!(
        cached.normalize(&marker("Small")),
        super::super::normalize(&marker("Small"), &defs)
    );
    assert_eq!(cached.entries.len(), 1, "a bypass cannot consume another request's cache room");
}

#[test]
fn aggregate_output_node_and_byte_caps_bound_multiple_entries() {
    for large_names in [false, true] {
        let mut defs = DatatypeDefs::new();
        for index in 0..16 {
            let name = format!("Many{index}");
            let mut ty = structure(&name, vec![Ty::u64(); if large_names { 1 } else { 1024 }]);
            if large_names {
                if let Ty::Adt { fields, .. } = &mut ty {
                    fields.make_mut()[0].0 = "x".repeat(MAX_RETAINED_BYTES / 3);
                }
            }
            defs.insert(name, ty);
        }
        let mut cached = Normalizer::new(&defs);
        for name in defs.keys() {
            assert_eq!(
                cached.normalize(&marker(name)),
                super::super::normalize(&marker(name), &defs)
            );
        }
        assert!(!cached.entries.is_empty());
        assert!(
            cached.entries.len() < defs.len(),
            "aggregate retention must stop before all roots"
        );
        assert!(cached.retained_nodes <= MAX_RETAINED_NODES);
        assert!(cached.retained_bytes <= MAX_RETAINED_BYTES);
        assert_eq!(cached.entries.len(), if large_names { 2 } else { 1 });
        if !large_names {
            assert_eq!(cached.retained_nodes, 1025, "the aggregate node cap binds first");
            assert!(cached.retained_bytes * 2 < MAX_RETAINED_BYTES);
        }
    }
}

#[test]
fn non_marker_requests_and_unaccounted_output_shapes_use_the_same_result() {
    let callable =
        Ty::FnPtr { sig: Box::new(FnSig { params: vec![Ty::u64()], ret: Box::new(Ty::Bool) }) };
    let definition =
        structure("Callable", vec![Ty::Ref { mutable: false, inner: Box::new(callable) }]);
    let defs = [("Callable".into(), definition.clone())].into();
    let mut cached = Normalizer::new(&defs);
    for input in [
        marker("Callable"),
        definition,
        Ty::Ref { mutable: false, inner: Box::new(marker("Callable")) },
    ] {
        for _ in 0..2 {
            assert_eq!(cached.normalize(&input), super::super::normalize(&input, &defs));
        }
    }
    assert!(cached.entries.is_empty());
    assert_eq!(cached.misses, 6);
}

#[test]
fn body_and_tuple_views_match_uncached_mapping_and_preserve_original_evidence() {
    let mut definition = structure("Value", vec![Ty::u64()]);
    if let Ty::Adt { arbitrary_precision, .. } = &mut definition {
        *arbitrary_precision = Some(AdtAuth::TotalDrop(None));
    }
    let defs: DatatypeDefs = [("Value".into(), definition.clone())].into();
    let body = VerifiableBody {
        locals: (0..4)
            .map(|index| LocalDecl {
                index,
                ty: marker("Value"),
                name: Some(format!("local{index}")),
            })
            .collect(),
        blocks: vec![],
        arg_count: 3,
        return_ty: marker("Value"),
        datatype_defs: defs.clone(),
    };
    let before = format!("{body:?}");
    let mut expected = body.clone();
    crate::physical_body_walk::map_body_types(&mut expected, &mut |ty| {
        super::super::normalize(ty, &defs)
    });
    let actual = super::super::body_view(&body);
    assert_eq!(actual.return_ty, expected.return_ty);
    assert_eq!(
        actual.locals.iter().map(|local| &local.ty).collect::<Vec<_>>(),
        expected.locals.iter().map(|local| &local.ty).collect::<Vec<_>>()
    );
    assert_eq!(actual.datatype_defs, defs);
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!(format!("{body:?}"), before);

    let row = TupleLayoutInfo {
        tuple: Ty::Tuple(vec![marker("Value")]),
        size: 8,
        align: 8,
        field_offsets: vec![0],
        field_sizes: vec![8],
        field_aligns: vec![8],
    };
    let target = Some(LayoutTarget {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        little_endian: true,
    });
    // Two distinct source keys collide after expansion with different coherent
    // layouts. The existing from_rows refusal must still remove both rows.
    let collision = TupleLayoutInfo {
        tuple: Ty::Tuple(vec![definition]),
        size: 16,
        field_offsets: vec![8],
        ..row.clone()
    };
    let layouts = TupleLayouts { target, entries: vec![row, collision] };
    let before = layouts.clone();
    let expected = TupleLayouts::from_rows(
        layouts.target.clone(),
        layouts
            .entries
            .iter()
            .map(|row| TupleLayoutInfo {
                tuple: super::super::normalize(&row.tuple, &defs),
                ..row.clone()
            })
            .collect(),
    );
    assert!(expected.is_empty(), "conflicting normalized keys retain their refusal");
    assert_eq!(*super::super::tuple_layouts_view(&layouts, &defs), expected);
    assert_eq!(layouts, before);
}
