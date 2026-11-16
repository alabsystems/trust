//! A shared reference may change inline UnsafeCell bytes. A unique initializer
//! is historical after such an escape, even though the local has one whole write.
use trust_types::{AdtKind, Place, Projection, Ty, VerifiableFunction};

fn stamped(name: &str, fields: Vec<(String, Ty)>, kind: AdtKind) -> Ty {
    let mut ty = Ty::adt(name, fields);
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(kind);
    }
    ty
}

pub fn cell() -> Ty {
    stamped(
        "core::cell::Cell<usize>",
        vec![(
            "value".into(),
            stamped(
                "core::cell::UnsafeCell<usize>",
                vec![("value".into(), Ty::usize())],
                AdtKind::Struct,
            ),
        )],
        AdtKind::Struct,
    )
}

/// The initialized local is moved from a parameter of the SAME type. The shared
/// borrow has the projected type, then an opaque user function receives it. No
/// uninitialized reads, mismatched borrow types, forged intrinsics or UB are needed.
pub fn fixture(root: Ty, projections: Vec<Projection>, borrowed: Ty) -> VerifiableFunction {
    let mut f: VerifiableFunction = serde_json::from_value(serde_json::json!({
        "name":"f", "def_path":"f",
        "span":{"file":"shared_cell_escape.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1},
        "body":{"arg_count":1,"return_ty":{"Int":{"width":64,"signed":false}},
            "locals":[], "blocks":[
                {"id":0,"stmts":[],"terminator":{"Call":{
                    "func":"poke", "args":[{"Copy":{"local":4,"projections":[]}}],
                    "dest":{"local":2,"projections":[]}, "target":1,
                    "span":{"file":"shared_cell_escape.rs","line_start":4,"col_start":1,"line_end":4,"col_end":1},
                    "atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},
                {"id":1,"stmts":[],"terminator":"Return"}
            ]}, "contracts":[]
    })).unwrap();
    f.body.locals = vec![
        (0, Ty::usize()),
        (1, root.clone()),
        (2, Ty::Unit),
        (3, root),
        (4, Ty::Ref { mutable: false, inner: Box::new(borrowed) }),
    ]
    .into_iter()
    .map(|(index, ty)| trust_types::LocalDecl { index, ty, name: None })
    .collect();
    let span = f.span.clone();
    f.body.blocks[0].stmts = vec![
        trust_types::Statement::Assign {
            place: Place { local: 3, projections: vec![] },
            rvalue: trust_types::Rvalue::Use(trust_types::Operand::Move(Place {
                local: 1,
                projections: vec![],
            })),
            span: span.clone(),
        },
        trust_types::Statement::Assign {
            place: Place { local: 4, projections: vec![] },
            rvalue: trust_types::Rvalue::Ref {
                mutable: false,
                place: Place { local: 3, projections },
            },
            span: span.clone(),
        },
    ];
    f.body.blocks[1].stmts.push(trust_types::Statement::Assign {
        place: Place { local: 0, projections: vec![] },
        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
            trust_types::ConstValue::Uint(7, 64),
        )),
        span,
    });
    f
}

pub fn cases() -> Vec<(&'static str, VerifiableFunction, bool)> {
    let scalar = Ty::usize();
    let cell = cell();
    let pair = Ty::Tuple(vec![cell.clone(), scalar.clone()]);
    let ptr = Ty::Ref { mutable: false, inner: Box::new(cell.clone()) };
    let raw = Ty::RawPtr { mutable: true, pointee: Box::new(cell.clone()) };
    let user = stamped("app::GridCell", vec![("x".into(), scalar.clone())], AdtKind::Struct);
    let union = stamped(
        "app::U",
        vec![("c".into(), cell.clone()), ("n".into(), scalar.clone())],
        AdtKind::Union,
    );
    let vec_ty: Ty =
        serde_json::from_str(r#"{"Seq":{"elem":{"Int":{"width":64,"signed":false}}}}"#).unwrap();
    let uv = stamped(
        "app::UV",
        vec![("v".into(), vec_ty.clone()), ("n".into(), scalar.clone())],
        AdtKind::Union,
    );
    vec![
        ("shared Cell", fixture(cell.clone(), vec![], cell.clone()), false),
        ("shared scalar", fixture(scalar.clone(), vec![], scalar.clone()), true),
        ("cell tuple whole", fixture(pair.clone(), vec![], pair.clone()), false),
        (
            "cell tuple field",
            fixture(pair.clone(), vec![Projection::Field(0)], cell.clone()),
            false,
        ),
        ("frozen sibling", fixture(pair, vec![Projection::Field(1)], scalar.clone()), true),
        ("shared pointer slot", fixture(ptr.clone(), vec![], ptr.clone()), true),
        ("shared pointee", fixture(ptr, vec![Projection::Deref], cell.clone()), true),
        ("raw pointee", fixture(raw, vec![Projection::Deref], cell.clone()), true),
        ("user GridCell fields", fixture(user.clone(), vec![], user), true),
        ("union cell field", fixture(union.clone(), vec![Projection::Field(0)], cell), false),
        ("union frozen field", fixture(union, vec![Projection::Field(1)], scalar), true),
        ("Vec named bytes", fixture(vec_ty.clone(), vec![], vec_ty.clone()), true),
        ("union Vec bytes", fixture(uv, vec![Projection::Field(0)], vec_ty), false),
    ]
}

pub fn runtime_cell_witness() -> (usize, usize) {
    let input = std::cell::Cell::new(0usize);
    let local = input;
    let before = local.get();
    let alias = &local;
    alias.set(1);
    (before, local.get())
}

#[test]
fn defined_cell_mutation_changes_the_initialized_value() {
    assert_eq!(runtime_cell_witness(), (0, 1));
}

#[test]
fn both_consumers_agree_on_typed_escapes_and_preserve_frozen_values() {
    for (name, f, unique) in cases() {
        let (count, definition, _) = trust_ir_bridge::local_defs_exact_for_test(&f, 3);
        assert_eq!(count, trust_types::ValueCount::Exactly(1), "{name}");
        assert_eq!(definition.is_some(), unique, "bridge: {name}");
        let vcgen = trust_vcgen::local_defs::unique_value_def(&f, 3);
        assert_eq!(vcgen.is_some(), unique, "vcgen: {name}");
        if let (Some(left), Some(right)) = (definition, vcgen) {
            assert!(std::ptr::eq(left, right), "initializer provenance: {name}");
        }
    }
}

#[test]
fn shared_place_coverage_retains_siblings_and_expands_union_overlap() {
    use trust_types::interior_mutability::shared_borrow_cell_places;
    for (name, f, unique) in cases() {
        let places = shared_borrow_cell_places(&f.body, &f.body.blocks[0].stmts[1]);
        assert_eq!(places.is_none(), unique, "{name}");
        if let Some((root, places)) = places {
            assert_eq!(root, 3);
            let projections = if name == "cell tuple whole" || name == "cell tuple field" {
                vec![Projection::Field(0)]
            } else {
                vec![]
            };
            assert_eq!(places, vec![Place { local: 3, projections }], "{name}");
        }
    }
}

#[test]
fn arrays_and_defined_datatypes_use_the_same_cell_channel() {
    use trust_types::interior_mutability::shared_borrow_cell_places;
    let leaf = cell();
    let array = Ty::Array { elem: Box::new(leaf.clone()), len: 2 };
    let f = fixture(
        array,
        vec![Projection::ConstantIndex { offset: 0, min_length: 2, from_end: false }],
        leaf.clone(),
    );
    assert!(trust_ir_bridge::local_defs_exact_for_test(&f, 3).1.is_none());
    assert!(trust_vcgen::local_defs::unique_value_def(&f, 3).is_none());
    let marker = Ty::Datatype { name: "Holder".into(), variants: vec![] };
    let definition = Ty::Datatype {
        name: "Holder".into(),
        variants: vec![(
            "Holder".into(),
            vec![("cell".into(), leaf.clone()), ("number".into(), Ty::usize())],
        )],
    };
    let mut cell_borrow = fixture(marker.clone(), vec![Projection::Field(0)], leaf);
    cell_borrow.body.datatype_defs.insert("Holder".into(), definition.clone());
    assert!(
        shared_borrow_cell_places(&cell_borrow.body, &cell_borrow.body.blocks[0].stmts[1])
            .is_some()
    );
    assert!(trust_ir_bridge::local_defs_exact_for_test(&cell_borrow, 3).1.is_none());
    let mut frozen_borrow = fixture(marker, vec![Projection::Field(1)], Ty::usize());
    frozen_borrow.body.datatype_defs.insert("Holder".into(), definition);
    assert!(
        shared_borrow_cell_places(&frozen_borrow.body, &frozen_borrow.body.blocks[0].stmts[1])
            .is_none()
    );
    assert!(trust_ir_bridge::local_defs_exact_for_test(&frozen_borrow, 3).1.is_some());
}

#[test]
fn unresolved_types_refuse_without_invalidating_a_known_frozen_borrow() {
    use trust_types::interior_mutability::shared_borrow_cell_places;
    let unknown = Ty::Datatype { name: "Unrecorded".into(), variants: vec![] };
    let f = fixture(unknown.clone(), vec![], unknown);
    assert!(shared_borrow_cell_places(&f.body, &f.body.blocks[0].stmts[1]).is_some());
    assert!(trust_ir_bridge::local_defs_exact_for_test(&f, 3).1.is_none());
    let f = fixture(Ty::usize(), vec![], Ty::usize());
    assert!(shared_borrow_cell_places(&f.body, &f.body.blocks[0].stmts[1]).is_none());
    assert!(trust_ir_bridge::local_defs_exact_for_test(&f, 3).1.is_some());
}

#[test]
fn wide_and_storage_policies_differ_only_for_pointee_borrows() {
    use trust_types::local_defs::{statement_escapes_local, statement_escapes_local_storage};
    let pointer = Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) };
    let mut f = fixture(pointer, vec![Projection::Deref], Ty::usize());
    let trust_types::Statement::Assign { rvalue: trust_types::Rvalue::Ref { mutable, .. }, .. } =
        &mut f.body.blocks[0].stmts[1]
    else {
        panic!()
    };
    *mutable = true;
    f.body.locals[4].ty = Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) };
    let statement = &f.body.blocks[0].stmts[1];
    assert!(statement_escapes_local(&f.body, statement, 3));
    assert!(!statement_escapes_local_storage(&f.body, statement, 3));
    for (_, f, unique) in cases() {
        let statement = &f.body.blocks[0].stmts[1];
        assert_eq!(statement_escapes_local(&f.body, statement, 3), !unique);
        assert_eq!(statement_escapes_local_storage(&f.body, statement, 3), !unique);
    }
}

#[test]
fn projection_step_preserves_variant_identity_and_subslice_failure() {
    use std::borrow::Cow;

    use trust_types::place_ty::place_ty_step;
    let ty = Ty::Datatype {
        name: "Either".into(),
        variants: vec![
            ("Frozen".into(), vec![("value".into(), Ty::usize())]),
            ("Cell".into(), vec![("value".into(), cell())]),
        ],
    };
    let defs = Default::default();
    let mut variant = None;
    assert!(
        place_ty_step(&defs, Cow::Borrowed(&ty), &Projection::Field(0), &mut variant).is_none()
    );
    let downcast =
        place_ty_step(&defs, Cow::Borrowed(&ty), &Projection::Downcast(1), &mut variant).unwrap();
    assert_eq!(
        place_ty_step(&defs, downcast, &Projection::Field(0), &mut variant).unwrap().as_ref(),
        &cell()
    );
    assert_eq!(variant, None);
    let array = Ty::Array { elem: Box::new(Ty::usize()), len: 2 };
    assert!(
        place_ty_step(
            &defs,
            Cow::Borrowed(&array),
            &Projection::Subslice { from: 0, to: 3, from_end: false },
            &mut variant
        )
        .is_none()
    );
    assert_eq!(
        place_ty_step(
            &defs,
            Cow::Borrowed(&array),
            &Projection::Subslice { from: 0, to: 1, from_end: false },
            &mut variant
        )
        .unwrap()
        .as_ref(),
        &Ty::Array { elem: Box::new(Ty::usize()), len: 1 }
    );
}
