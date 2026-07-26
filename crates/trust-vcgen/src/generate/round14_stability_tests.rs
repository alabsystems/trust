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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn struct_scalar_leaf_suffixes_enumerate_fields_and_array_elements() {
    use super::float_scalar_leaf_suffixes;
    let vec3 = Ty::Adt { adt_kind: None, layout: None, 
        name: "Vec3".into(),
        fields: vec![
            ("x".into(), Ty::f64_ty()),
            ("y".into(), Ty::f64_ty()),
            ("z".into(), Ty::f64_ty()),
        ],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    // Vec3 -> three field leaves `.0 .1 .2`.
    let leaves = float_scalar_leaf_suffixes(&vec3, 6);
    assert_eq!(leaves.len(), 3);
    assert!(leaves.iter().all(|l| matches!(l.as_slice(), [Projection::Field(_)])));
    // A bare f64 is its own leaf (empty suffix).
    assert_eq!(float_scalar_leaf_suffixes(&Ty::f64_ty(), 6), vec![vec![]]);
    // Mat4 { cols: [Vec4; 4] } — nested field . array . field, 16 f64 leaves.
    let vec4 = Ty::Adt { adt_kind: None, layout: None, 
        name: "Vec4".into(),
        fields: (0..4).map(|i| (format!("f{i}"), Ty::f64_ty())).collect(),
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let mat4 = Ty::Adt { adt_kind: None, layout: None,
        name: "Mat4".into(),
        fields: vec![("cols".into(), Ty::Array { elem: Box::new(vec4), len: 4 })],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let m_leaves = float_scalar_leaf_suffixes(&mat4, 6);
    assert_eq!(m_leaves.len(), 16, "Mat4 has 16 f64 leaves");
    assert!(m_leaves.iter().all(|l| matches!(
        l.as_slice(),
        [Projection::Field(0), Projection::ConstantIndex { .. }, Projection::Field(_)]
    )));
    // A non-f64 struct (all-int) yields NO f64 leaves.
    let ints = Ty::Adt { adt_kind: None, layout: None, 
        name: "P".into(),
        fields: vec![("a".into(), Ty::Int { width: 32, signed: true })],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    assert!(float_scalar_leaf_suffixes(&ints, 6).is_empty());
}

#[test]
fn raw_ptr_deref_is_flagged_shared_ref_is_not() {
    let struct_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "V".into(),
        fields: vec![("x".into(), Ty::f64_ty())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    // `(*p).0` with `p: *mut V` — aliasable, must be flagged unstable.
    let raw =
        func_with_param(Ty::RawPtr { pointee: Box::new(struct_ty.clone()), mutable: true });
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
    let by_value = func_with_param(Ty::Adt { adt_kind: None, layout: None, 
        name: "V".into(),
        fields: vec![("x".into(), Ty::f64_ty())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, });
    assert!(
        !place_reads_through_raw_ptr(
            &by_value,
            &Place { local: 1, projections: vec![Projection::Field(0)] }
        ),
        "by-value field read must NOT be flagged"
    );
}
