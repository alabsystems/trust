use trust_types::{LocalDecl, Place, Projection, Ty, VerifiableBody, VerifiableFunction};

use super::place_reads_through_raw_ptr;

fn func_with_param(ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::f".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty, name: Some("p".into()) },
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: Ty::f64_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn struct_scalar_leaf_chains_resolve_fields_and_array_elements() {
    use super::float_leaf_chain;
    let vec3 = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        name: "Vec3".into(),
        fields: vec![
            ("x".into(), Ty::f64_ty()),
            ("y".into(), Ty::f64_ty()),
            ("z".into(), Ty::f64_ty()),
        ]
        .into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    let func = func_with_param(vec3.clone());
    // Vec3 -> each field `.0 .1 .2` is a leaf; `.3` does not exist.
    for i in 0..3 {
        assert_eq!(
            float_leaf_chain(&func, &vec3, &[Projection::Field(i)], 6),
            Some(vec![Projection::Field(i)])
        );
    }
    assert_eq!(float_leaf_chain(&func, &vec3, &[Projection::Field(3)], 6), None);
    // The whole struct is not a leaf; a bare f64 is its own leaf (empty chain).
    assert_eq!(float_leaf_chain(&func, &vec3, &[], 6), None);
    assert_eq!(float_leaf_chain(&func, &Ty::f64_ty(), &[], 6), Some(vec![]));
    // Mat4 { cols: [Vec4; 4] } — nested field . array . field.
    let vec4 = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        name: "Vec4".into(),
        fields: (0..4).map(|i| (format!("f{i}"), Ty::f64_ty())).collect(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    let mat = |len: u64| Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        name: "Mat".into(),
        fields: vec![("cols".into(), Ty::Array { elem: Box::new(vec4.clone()), len })].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    // Any spelling of lane k (a constant index of any `min_length`) resolves to
    // the one canonical step `[k; min = len]`.
    let read = |lane: usize, min_length: usize| {
        [
            Projection::Field(0),
            Projection::ConstantIndex { offset: lane, min_length, from_end: false },
            Projection::Field(1),
        ]
    };
    let canonical = |lane: usize, len: usize| {
        vec![
            Projection::Field(0),
            Projection::ConstantIndex { offset: lane, min_length: len, from_end: false },
            Projection::Field(1),
        ]
    };
    assert_eq!(float_leaf_chain(&func, &mat(4), &read(2, 3), 6), Some(canonical(2, 4)));
    assert_eq!(float_leaf_chain(&func, &mat(4), &read(4, 4), 6), None, "lane 4 of 4");
    // The retired enumeration stopped at 16 lanes per array. Resolution walks
    // the ONE chain a read names, so a lane far past that is the same three
    // steps (kept to 2^16 lanes so a regression that enumerated would still
    // fail cheaply).
    let huge = 1u64 << 16;
    let lane = 40_000usize;
    assert_eq!(
        float_leaf_chain(&func, &mat(huge), &read(lane, 1), 6),
        Some(canonical(lane, huge as usize))
    );
    // A from-end index is not a leaf step (its contract spelling differs).
    assert_eq!(
        float_leaf_chain(
            &func,
            &mat(4),
            &[
                Projection::Field(0),
                Projection::ConstantIndex { offset: 1, min_length: 4, from_end: true },
                Projection::Field(1),
            ],
            6
        ),
        None
    );
    // The nesting depth still bounds the walk (type text, not a length).
    assert_eq!(float_leaf_chain(&func, &mat(4), &read(1, 4), 2), None);
    // A non-f64 struct (all-int) has NO f64 leaves.
    let ints = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        name: "P".into(),
        fields: vec![("a".into(), Ty::Int { width: 32, signed: true })].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    assert_eq!(float_leaf_chain(&func, &ints, &[Projection::Field(0)], 6), None);
}

#[test]
fn raw_ptr_deref_is_flagged_shared_ref_is_not() {
    let struct_ty = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        name: "V".into(),
        fields: vec![("x".into(), Ty::f64_ty())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    // `(*p).0` with `p: *mut V` — aliasable, must be flagged unstable.
    let raw = func_with_param(Ty::RawPtr { pointee: Box::new(struct_ty.clone()), mutable: true });
    let deref_field =
        Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    assert!(place_reads_through_raw_ptr(&raw, &deref_field), "raw-ptr deref must be flagged");
    // `(*p).0` with `p: &V` — the shared-ref pointee is immutable-for-lifetime,
    // NOT flagged (the existing `<p>*` discipline handles it).
    let shared = func_with_param(Ty::Ref { inner: Box::new(struct_ty), mutable: false });
    assert!(
        !place_reads_through_raw_ptr(&shared, &deref_field),
        "shared-ref deref must NOT be flagged"
    );
    // A bare by-value field read `p.0` (no deref) is never flagged.
    let by_value = func_with_param(Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        name: "V".into(),
        fields: vec![("x".into(), Ty::f64_ty())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    });
    assert!(
        !place_reads_through_raw_ptr(
            &by_value,
            &Place { local: 1, projections: vec![Projection::Field(0)] }
        ),
        "by-value field read must NOT be flagged"
    );
}
