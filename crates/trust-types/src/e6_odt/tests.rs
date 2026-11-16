// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::{BasicBlock, BlockId, LocalDecl, SourceSpan, VariantDef, VerifiableBody};

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

pub fn enumeration() -> VerifiableFunction {
    let ty = Ty::adt_enum(
        "test::Phase",
        vec![
            VariantDef { name: "Ready".into(), discriminant: 42, fields: vec![] },
            VariantDef { name: "Waiting".into(), discriminant: 3, fields: vec![] },
        ],
    );
    VerifiableFunction {
        name: "phase".into(),
        def_path: "test::phase".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            arg_count: 1,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
            locals: [Ty::Bool, ty, Ty::Int { width: 8, signed: false }]
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![
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
                    stmts: vec![assign(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(true))))],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(false))))],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Unreachable },
            ],
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn constructor_order_is_distinct_from_switch_and_discriminant_order() {
    let f = enumeration();
    let Some(Body::Cases { param: 0, branches }) = read(&f) else { panic!("enum reader") };
    assert_eq!(branches, vec![Leaf::Bool(true), Leaf::Bool(false)]);
    assert!(crate::facet_inference::infer_facets(&[f])["test::phase"].all());
}

#[test]
fn if_converted_enum_match_still_reads_as_cases() {
    let mut f = enumeration();
    f.body.blocks[0].stmts.push(assign(
        0,
        Rvalue::BinaryOp(
            BinOp::Eq,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(42, 8)),
        ),
    ));
    f.body.blocks[0].terminator = Terminator::Return;
    let Some(Body::Cases { param: 0, branches }) = read(&f) else { panic!("if-converted enum") };
    assert_eq!(branches, vec![Leaf::Bool(true), Leaf::Bool(false)]);
}

#[test]
fn constant_folded_enum_match_still_has_every_constructor_branch() {
    let mut f = enumeration();
    f.body.blocks[0].stmts =
        vec![assign(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(true))))];
    f.body.blocks[0].terminator = Terminator::Return;
    let Some(Body::Cases { param: 0, branches }) = read(&f) else { panic!("folded enum") };
    assert_eq!(branches, vec![Leaf::Bool(true), Leaf::Bool(true)]);
}

#[test]
fn tag_identity_and_concrete_bool_cast_preserve_enum_match_results() {
    let mut f = enumeration();
    let u8_ty = Ty::Int { width: 8, signed: false };
    f.body.return_ty = u8_ty.clone();
    f.body.locals[0].ty = u8_ty.clone();
    f.body.blocks.truncate(1);
    f.body.blocks[0].stmts = vec![assign(0, Rvalue::Discriminant(Place::local(1)))];
    f.body.blocks[0].terminator = Terminator::Return;
    let Some(Body::Cases { branches, .. }) = read(&f) else { panic!("tag identity") };
    assert_eq!(branches, vec![Leaf::Int(42), Leaf::Int(3)]);

    f.body.locals.push(LocalDecl { index: 3, ty: Ty::Bool, name: None });
    f.body.blocks[0].stmts = vec![
        assign(2, Rvalue::Discriminant(Place::local(1))),
        assign(
            3,
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(42, 8)),
            ),
        ),
        assign(0, Rvalue::Cast(Operand::Copy(Place::local(3)), u8_ty)),
    ];
    let Some(Body::Cases { branches, .. }) = read(&f) else { panic!("boolean cast") };
    assert_eq!(branches, vec![Leaf::Int(1), Leaf::Int(0)]);
    let mut wrong = f.clone();
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, rhs), .. } =
        &mut wrong.body.blocks[0].stmts[1]
    else {
        unreachable!()
    };
    *rhs = Operand::Constant(ConstValue::Uint(42, 64));
    assert!(read(&wrong).is_none(), "tag comparison must retain the u8 operand type");

    let i8_ty = Ty::Int { width: 8, signed: true };
    f.body.return_ty = i8_ty.clone();
    f.body.locals[0].ty = i8_ty.clone();
    let Ty::Adt { variants, .. } = &mut f.body.locals[1].ty else { unreachable!() };
    variants.make_mut()[0].discriminant = 250;
    f.body.blocks[0].stmts = vec![
        assign(2, Rvalue::Discriminant(Place::local(1))),
        assign(0, Rvalue::Cast(Operand::Copy(Place::local(2)), i8_ty)),
    ];
    let Some(Body::Cases { branches, .. }) = read(&f) else { panic!("signed tag cast") };
    assert_eq!(branches, vec![Leaf::Int(-6), Leaf::Int(3)]);
}

#[test]
fn missing_constructor_guard_cycle_effect_and_malformed_identity_refuse() {
    let f = enumeration();
    let mut mutants = vec![];
    let mut missing = f.clone();
    let Terminator::SwitchInt { targets, .. } = &mut missing.body.blocks[0].terminator else {
        unreachable!()
    };
    targets.pop();
    mutants.push(missing);
    let mut guard = f.clone();
    guard.body.blocks[1].terminator = Terminator::SwitchInt {
        discr: Operand::Constant(ConstValue::Bool(true)),
        targets: vec![(1, BlockId(2))],
        otherwise: BlockId(3),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    mutants.push(guard);
    let mut cycle = f.clone();
    cycle.body.blocks[2].terminator = Terminator::Goto(BlockId(0));
    mutants.push(cycle);
    let mut write = f.clone();
    write.body.blocks[1]
        .stmts
        .push(assign(1, Rvalue::Use(Operand::Constant(ConstValue::Bool(false)))));
    mutants.push(write);
    let mut bad = f.clone();
    bad.body.locals[2].index = 1;
    mutants.push(bad);
    let mut bad = f.clone();
    bad.body.blocks[1].id = BlockId(2);
    mutants.push(bad);
    let mut bad = f.clone();
    bad.body.locals[2].ty = Ty::Int { width: 8, signed: true };
    mutants.push(bad);
    for mutant in mutants {
        assert!(read(&mutant).is_none(), "{mutant:?}");
    }
}

#[test]
fn struct_is_a_nominal_projection_and_no_borrow_is_read() {
    let mut f = enumeration();
    f.body.locals.truncate(2);
    f.body.locals[1].ty =
        Ty::adt("test::Pair", vec![("other".into(), Ty::Bool), ("selected".into(), Ty::Bool)]);
    f.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![assign(
            0,
            Rvalue::Use(Operand::Copy(Place { local: 1, projections: vec![Projection::Field(1)] })),
        )],
        terminator: Terminator::Return,
    }];
    assert!(matches!(read(&f), Some(Body::Projection(Leaf::Field { param: 0, field: 1 }))));
    let mut union = f.clone();
    let Ty::Adt { adt_kind, .. } = &mut union.body.locals[1].ty else { unreachable!() };
    *adt_kind = Some(crate::AdtKind::Union);
    assert!(read(&union).is_none(), "union storage is not a nominal scalar product");
    let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(p)), .. } =
        &mut f.body.blocks[0].stmts[0]
    else {
        unreachable!()
    };
    p.projections.insert(0, Projection::Deref);
    assert!(read(&f).is_none());
}
