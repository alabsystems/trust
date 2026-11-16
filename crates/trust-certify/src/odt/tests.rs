// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use trust_odt::{Field, IsoState, TypeKey, Variant};

use super::*;

fn declaration(shape: Shape) -> RustDecl {
    RustDecl { key: TypeKey { stable_crate_id: 17, local_def_path_hash: 31 }, shape }
}
fn enumeration() -> RustDecl {
    declaration(Shape::FieldlessEnum {
        variants: vec![
            Variant { name: "Zebra".into(), discriminant: "-3".into() },
            Variant { name: "Alpha".into(), discriminant: "42".into() },
        ],
    })
}
fn record() -> RustDecl {
    declaration(Shape::ScalarStruct {
        fields: vec![
            Field { name: "right".into(), scalar: Scalar::U32 },
            Field { name: "left".into(), scalar: Scalar::U32 },
        ],
    })
}

#[test]
fn every_generated_face_passes_its_own_kernel_b1() {
    let base = Environment::with_prelude();
    let mut cases = vec![
        enumeration(),
        record(),
        declaration(Shape::FieldlessEnum { variants: vec![] }),
        declaration(Shape::ScalarStruct { fields: vec![] }),
    ];
    for scalar in [
        Scalar::Bool,
        Scalar::U8,
        Scalar::U16,
        Scalar::U32,
        Scalar::U64,
        Scalar::I8,
        Scalar::I16,
        Scalar::I32,
        Scalar::I64,
    ] {
        cases.push(declaration(Shape::ScalarStruct {
            fields: vec![Field { name: "0".into(), scalar }],
        }));
    }
    for decl in cases {
        let mut env = base.clone();
        let checked = generate_into(&mut env, decl.clone()).unwrap();
        assert_eq!(checked.entry().iso(), IsoState::Pending);
        assert_eq!(checked.kernel_type(), Expr::const_str(&decl.key.kernel_name()));
        for (goal, proof) in checked.evidence() {
            assert!(env.audit_certification(goal, proof).is_certified());
        }
        assert!(
            env.inductive_info(&Name::from_string(&decl.key.kernel_name()))
                .unwrap()
                .cases_on_name
                .is_some()
        );
        // A fresh importer earns the checks from the actual round-tripped bytes.
        let imported =
            readmit_into(&mut base.clone(), &decl, &checked.entry().encode().unwrap()).unwrap();
        assert_eq!(imported.constructor_names(), checked.constructor_names());
    }
}

fn refuses_mutant(decl: RustDecl, mutate: impl FnOnce(&mut LogicalFace)) {
    let mut face = decl.logical_face();
    mutate(&mut face);
    // This envelope has an honest checksum. Integrity alone cannot detect it.
    let bytes = Entry::candidate(decl.clone(), face).unwrap().encode().unwrap();
    let mut env = Environment::with_prelude();
    let err = readmit_into(&mut env, &decl, &bytes).unwrap_err();
    assert!(err.contains("refused by kernel"), "{err}");
    assert!(env.get_inductive(&Name::from_string(&decl.key.kernel_name())).is_none());
}

#[test]
fn swapped_constructors_are_refused_by_the_kernel() {
    refuses_mutant(enumeration(), |f| {
        let Shape::FieldlessEnum { variants } = &mut f.shape else { unreachable!() };
        variants.swap(0, 1);
    });
}

#[test]
fn swapped_discriminants_are_refused_separately_from_constructor_shape() {
    refuses_mutant(enumeration(), |f| {
        let Shape::FieldlessEnum { variants } = &mut f.shape else { unreachable!() };
        let tag = variants[0].discriminant.clone();
        variants[0].discriminant = variants[1].discriminant.clone();
        variants[1].discriminant = tag;
    });
}

#[test]
fn swapped_same_typed_struct_fields_are_refused_by_the_kernel() {
    refuses_mutant(record(), |f| {
        let Shape::ScalarStruct { fields } = &mut f.shape else { unreachable!() };
        fields.swap(0, 1);
    });
}

#[test]
fn swapped_tuple_positions_and_scalar_mutants_are_refused() {
    let decl = declaration(Shape::ScalarStruct {
        fields: vec![
            Field { name: "0".into(), scalar: Scalar::U16 },
            Field { name: "1".into(), scalar: Scalar::U16 },
        ],
    });
    refuses_mutant(decl, |f| {
        let Shape::ScalarStruct { fields } = &mut f.shape else { unreachable!() };
        fields.swap(0, 1);
    });
    for scalar in [Scalar::U64, Scalar::I32] {
        refuses_mutant(record(), |f| {
            let Shape::ScalarStruct { fields } = &mut f.shape else { unreachable!() };
            fields[0].scalar = scalar;
        });
    }
}

#[test]
fn transported_rust_datum_cannot_replace_the_compilers_own_identity() {
    let decl = record();
    let mut other = decl.clone();
    other.key.stable_crate_id += 1;
    let bytes = Entry::generate(other).unwrap().encode().unwrap();
    assert!(
        readmit_into(&mut Environment::with_prelude(), &decl, &bytes)
            .unwrap_err()
            .contains("TypeKey")
    );
}

#[test]
fn exported_cases_on_and_projection_compute_in_the_actual_kernel() {
    let mut env = Environment::with_prelude();
    let checked = generate_into(&mut env, enumeration()).unwrap();
    let motive = Expr::lam(BinderInfo::Default, checked.kernel_type(), Expr::const_str("Nat"));
    for (i, expected) in [11, 22].into_iter().enumerate() {
        let term = Expr::apps(
            Expr::const_(
                Name::from_string(&checked.cases_on_name()),
                vec![Level::succ(Level::zero())],
            ),
            [
                motive.clone(),
                Expr::const_str(&checked.constructor_names()[i]),
                Expr::nat_lit(11),
                Expr::nat_lit(22),
            ],
        );
        check_equality(&env, term, Expr::nat_lit(expected)).unwrap();
    }

    let mut env = Environment::with_prelude();
    let decl = declaration(Shape::ScalarStruct {
        fields: vec![
            Field { name: "right".into(), scalar: Scalar::Bool },
            Field { name: "left".into(), scalar: Scalar::Bool },
        ],
    });
    let checked = generate_into(&mut env, decl).unwrap();
    let value = Expr::apps(
        Expr::const_str(&checked.constructor_names()[0]),
        [Expr::const_str("Bool.false"), Expr::const_str("Bool.true")],
    );
    let (index, scalar) = checked.field("left").unwrap();
    assert_eq!((index, scalar), (1, Scalar::Bool));
    let projection =
        Expr::proj(Name::from_string(&checked.entry().logical_face.kernel_name), index, value);
    let bool_ty = Expr::const_str("Bool");
    let yes = Expr::const_str("Bool.true");
    let level = Level::succ(Level::zero());
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [bool_ty.clone(), projection, yes.clone()],
    );
    let proof = Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![level]), [bool_ty, yes]);
    clean_kernel::TypeChecker::new(&env).check_type(&proof, &goal).unwrap();
    assert!(env.audit_certification(&goal, &proof).is_certified());
}
