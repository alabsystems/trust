// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use trust_odt::{Field, TypeKey, Variant};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, VariantDef, VerifiableBody,
};

use super::*;
use crate::clean_island::CleanIslandSession;

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}
fn function(types: Vec<Ty>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "kernel".into(),
        def_path: "test::kernel".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: types[0].clone(),
            locals: types
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            arg_count: 1,
            blocks,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}
fn input(name: &str, shape: Shape) -> FaceInput {
    let declaration =
        RustDecl { key: TypeKey { stable_crate_id: 33, local_def_path_hash: 44 }, shape };
    let transport = trust_odt::Entry::generate(declaration.clone()).unwrap().encode().unwrap();
    FaceInput { rust_path: format!("test::{name}"), declaration, transport }
}
fn table(func: &VerifiableFunction) -> trust_spec_elab::FacetTable {
    let inferred = trust_types::facet_inference::infer_facets(std::slice::from_ref(func));
    assert!(inferred[&func.def_path].all());
    let mut facets = trust_spec_elab::FacetTable::new();
    facets.insert(
        &func.def_path,
        trust_spec_elab::FnFacets::from_structural_certificates(
            true,
            true,
            true,
            true,
            "closed ODT test",
        ),
    );
    facets
}
fn enum_fixture(mutant: bool) -> (FaceInput, VerifiableFunction) {
    let variants = vec![
        VariantDef { name: "Ready".into(), discriminant: 42, fields: vec![] },
        VariantDef { name: "Waiting".into(), discriminant: 3, fields: vec![] },
    ];
    let face = input(
        "Phase",
        Shape::FieldlessEnum {
            variants: variants
                .iter()
                .map(|v| Variant { name: v.name.clone(), discriminant: v.discriminant.to_string() })
                .collect(),
        },
    );
    let func = function(
        vec![Ty::Bool, Ty::adt_enum("test::Phase", variants), Ty::Int { width: 8, signed: false }],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(2, Rvalue::Discriminant(Place::local(1)))],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(3, BlockId(2)), (42, BlockId(1))],
                    otherwise: BlockId(3),
                    exhaustive_enum_unreachable: true,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(!mutant))))],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(false))))],
                terminator: Terminator::Return,
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Unreachable },
        ],
    );
    (face, func)
}

#[test]
fn enum_import_is_cases_on_and_tag_bridge_is_derivable_with_mutant_control() {
    for mutant in [false, true] {
        let (face, func) = enum_fixture(mutant);
        let mut session = CleanIslandSession::new();
        let admitted = session
            .admit_odt_program_functions(&[face], std::slice::from_ref(&func), &table(&func))
            .unwrap();
        assert_eq!(admitted.len(), 1);
        let outcome = session.check(
            "\
          def tag_kernel (t : UInt8) : Bool := t == (42 : UInt8)\n\
          theorem bridge (p : trust_type_test__Phase) :\n\
            trust_import_test__kernel p = tag_kernel (trust_type_test__Phase.toTag p) := by\n\
            cases p <;> rfl\n",
        );
        assert_eq!(outcome.is_rejected(), mutant, "{outcome:?}");
    }
}

#[test]
fn projection_preserves_named_field_identity_with_mutant_control() {
    for mutant in [false, true] {
        let face = input(
            "Pair",
            Shape::ScalarStruct {
                fields: vec![
                    Field { name: "right".into(), scalar: Scalar::Bool },
                    Field { name: "left".into(), scalar: Scalar::Bool },
                ],
            },
        );
        let func = function(
            vec![
                Ty::Bool,
                Ty::adt("test::Pair", vec![("right".into(), Ty::Bool), ("left".into(), Ty::Bool)]),
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    0,
                    Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Field(if mutant { 0 } else { 1 })],
                    })),
                )],
                terminator: Terminator::Return,
            }],
        );
        let mut session = CleanIslandSession::new();
        session
            .admit_odt_program_functions(&[face], std::slice::from_ref(&func), &table(&func))
            .unwrap();
        let outcome = session.check("theorem exact (p : trust_type_test__Pair) : trust_import_test__kernel p = trust_type_test__Pair.fields.left p := rfl");
        assert_eq!(outcome.is_rejected(), mutant, "{outcome:?}");
    }
}

#[test]
fn expected_rust_declaration_and_extracted_type_must_agree() {
    let (mut face, func) = enum_fixture(false);
    let Shape::FieldlessEnum { variants } = &mut face.declaration.shape else { unreachable!() };
    variants.swap(0, 1);
    face.transport =
        trust_odt::Entry::generate(face.declaration.clone()).unwrap().encode().unwrap();
    let mut session = CleanIslandSession::new();
    assert!(
        session
            .admit_odt_program_functions(&[face], std::slice::from_ref(&func), &table(&func))
            .unwrap_err()
            .contains("disagrees")
    );
    // Atomic failure registered no counterfeit import or aliases.
    assert!(
        session
            .check("theorem absent : trust_import_test__kernel = trust_import_test__kernel := rfl")
            .is_rejected()
    );
}

#[test]
fn rust_member_names_do_not_collide_with_generated_helpers() {
    for reserved in ["casesOn", "toTag", "mk"] {
        let (mut face, mut func) = enum_fixture(false);
        let Shape::FieldlessEnum { variants } = &mut face.declaration.shape else { unreachable!() };
        variants[0].name = reserved.into();
        let Ty::Adt { variants, .. } = &mut func.body.locals[1].ty else { unreachable!() };
        variants.make_mut()[0].name = reserved.into();
        face.transport =
            trust_odt::Entry::generate(face.declaration.clone()).unwrap().encode().unwrap();
        let mut session = CleanIslandSession::new();
        session
            .admit_odt_program_functions(&[face], std::slice::from_ref(&func), &table(&func))
            .unwrap();
        let proof = format!(
            "theorem member_tag : trust_type_test__Phase.toTag trust_type_test__Phase.constructors.{reserved} = (42 : UInt8) := rfl\ntheorem member_body : trust_import_test__kernel trust_type_test__Phase.constructors.{reserved} = true := rfl"
        );
        let outcome = session.check(&proof);
        assert!(!outcome.is_rejected(), "{reserved}: {outcome:?}");
    }
    let fields = vec!["mk", "casesOn", "toTag"];
    let face = input(
        "Pair",
        Shape::ScalarStruct {
            fields: fields
                .iter()
                .map(|n| Field { name: (*n).into(), scalar: Scalar::Bool })
                .collect(),
        },
    );
    let func = function(
        vec![
            Ty::Bool,
            Ty::adt("test::Pair", fields.iter().map(|n| ((*n).into(), Ty::Bool)).collect()),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                0,
                Rvalue::Use(Operand::Copy(Place {
                    local: 1,
                    projections: vec![Projection::Field(1)],
                })),
            )],
            terminator: Terminator::Return,
        }],
    );
    let mut session = CleanIslandSession::new();
    session
        .admit_odt_program_functions(&[face], std::slice::from_ref(&func), &table(&func))
        .unwrap();
    let outcome = session.check("theorem reserved_projection (p : trust_type_test__Pair) : trust_import_test__kernel p = trust_type_test__Pair.fields.casesOn p := rfl\ntheorem reserved_computation : trust_type_test__Pair.fields.casesOn (trust_type_test__Pair.mk false true false) = true := rfl");
    assert!(!outcome.is_rejected(), "{outcome:?}");
}

/// TG16: an island that squats a name the ODT reader generates is refused at its own
/// declaration, naming the reserved namespace, before admission runs. The session is then
/// tainted, so admission mints nothing; before the reservation the island was accepted and the
/// later mint failed with a spanless `DuplicateName` naming neither the island nor the rule.
/// Control: the same declaration under the user's own name is accepted, and admission and the
/// enum bridge theorem still go through.
#[test]
fn an_island_squatting_a_generated_alias_is_refused_at_its_declaration() {
    let (face, func) = enum_fixture(false);
    let mut squat = CleanIslandSession::new();
    let batch = squat.check_all(&["def trust_type_test__Phase.toTag (n : Nat) : UInt8 := 0"]);
    assert!(batch.is_rejected(), "{:?}", batch.outcomes);
    assert!(
        batch.outcomes[0].errors.iter().any(|e| e.message.contains("`trust_type_*`")),
        "{:?}",
        batch.outcomes
    );
    let admitted = squat
        .admit_odt_program_functions(&[face], std::slice::from_ref(&func), &table(&func))
        .expect("a tainted session mints nothing rather than failing on a duplicate name");
    assert!(admitted.is_empty(), "{admitted:?}");

    let (face, func) = enum_fixture(false);
    let mut own = CleanIslandSession::new();
    let batch = own.check_all(&["def test_phase_tag (n : Nat) : UInt8 := 0"]);
    assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
    let admitted = own
        .admit_odt_program_functions(&[face], std::slice::from_ref(&func), &table(&func))
        .unwrap();
    assert_eq!(admitted.len(), 1);
    let outcome = own.check(
        "\
      def tag_kernel (t : UInt8) : Bool := t == (42 : UInt8)\n\
      theorem bridge (p : trust_type_test__Phase) :\n\
        trust_import_test__kernel p = tag_kernel (trust_type_test__Phase.toTag p) := by\n\
        cases p <;> rfl\n",
    );
    assert!(!outcome.is_rejected(), "{outcome:?}");
}
