//! Synthetic physical-enum inputs for the production body-table lowering path.
//! These are not extracted Clean bodies or Rust-correspondence certificates.

use trust_ir::inst::Inst;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty as IrTy;
use trust_ir::{Constant, Module, ProofAnnotation};
use trust_ir_build::validate_module;
use trust_types::{
    AdtKind, AggregateKind, BasicBlock, BlockId, ConstValue, EnumLayoutInfo, EnumReprHint,
    EnumTagEncodingInfo, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VariantDef, VerifiableBody, VerifiableFunction,
};

use crate::lower::lower_to_trust_ir;

const ENUM: &str = "synthetic_physical::Choice";

fn marker() -> Ty {
    Ty::Datatype { name: ENUM.into(), variants: vec![] }
}

fn definition() -> Ty {
    Ty::Adt {
        name: ENUM.into(),
        fields: vec![("__tag".into(), Ty::isize()), ("__v0_0".into(), Ty::i64())].into(),
        variants: vec![
            VariantDef {
                name: "Payload".into(),
                discriminant: 11,
                fields: vec![("0".into(), Ty::i64())],
            },
            VariantDef { name: "Empty".into(), discriminant: 37, fields: vec![] },
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: Some(Some(EnumReprHint::U8)),
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: None,
        enum_layout: Some(Box::new(EnumLayoutInfo {
            encoding: EnumTagEncodingInfo::Direct { tag_offset: 0, tag_ty: EnumReprHint::U8 },
            size: 16,
            align: 8,
            variant_field_offsets: vec![vec![8], vec![]],
        })),
        adt_kind: Some(AdtKind::Enum),
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn construction(variant: usize) -> Statement {
    assign(
        Place::local(1),
        Rvalue::Aggregate(
            AggregateKind::Adt { name: ENUM.into(), variant, active_field: None, args: None },
            if variant == 0 { vec![Operand::Constant(ConstValue::Int(41))] } else { vec![] },
        ),
    )
}

fn borrow(mutable: bool) -> Statement {
    assign(Place::local(2), Rvalue::Ref { mutable, place: Place::local(1) })
}

fn dereference() -> Place {
    Place { local: 2, projections: vec![Projection::Deref] }
}

fn fixture(result: Ty, mutable: bool, stmts: Vec<Statement>) -> VerifiableFunction {
    VerifiableFunction {
        name: "physical_enum_fixture".into(),
        def_path: "synthetic_physical::physical_enum_fixture".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: result.clone(), name: None },
                LocalDecl { index: 1, ty: marker(), name: Some("value".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable, inner: Box::new(marker()) },
                    name: Some("reference".into()),
                },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 0,
            return_ty: result,
            datatype_defs: [(ENUM.into(), definition())].into(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn instructions(module: &Module) -> impl Iterator<Item = &Inst> {
    module.functions[0].blocks.iter().flat_map(|block| &block.body).map(|node| &node.inst)
}

/// The bridge spells a reference as a `Copy` of the place address at `Ptr`
/// carrying the borrow `claim`, and never as a permission instruction (trust-ir
/// docs/SPEC_RATIFICATIONS.md, "A Rust reference carries no permission
/// instruction"). True when the module has such a reference and no `Borrow`,
/// `BorrowMut` or `EndBorrow` at all.
fn spells_reference(module: &Module, claim: ProofAnnotation) -> bool {
    let nodes = || {
        module
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.body.iter())
    };
    nodes().any(|node| {
        matches!(node.inst, Inst::Copy { ty: IrTy::Ptr, .. }) && node.proofs.contains(&claim)
    }) && !nodes().any(|node| {
        matches!(node.inst, Inst::Borrow { .. } | Inst::BorrowMut { .. } | Inst::EndBorrow { .. })
    })
}

fn checked(input: &VerifiableFunction) -> Module {
    let before = input.content_hash();
    let module = lower_to_trust_ir(input).expect("synthetic physical enum lowers");
    assert_eq!(input.content_hash(), before);
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "enum output must validate: {errors:?}");
    assert_eq!(module.enums.len(), 1);
    let definition = &module.enums[0];
    assert_eq!(definition.effective_discriminants(), Some(vec![11, 37]));
    let layout = definition.layout.as_ref().expect("physical enum layout retained");
    assert_eq!((layout.size, layout.align), (16, 8));
    assert_eq!(layout.variant_field_offsets, vec![vec![8], vec![]]);
    assert!(matches!(layout.encoding, trust_ir::EnumTagEncoding::Direct { tag_offset: 0 }));
    // Undef used as a temporary aggregate seed is not a field fact. No
    // consumer-typed opaque-read havoc may replace the tested precise reads.
    assert!(
        !module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .any(|node| node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc))
    );
    module
}

fn returns(module: &Module, ty: IrTy, value: i128) {
    let outcome = Interpreter::with_module(module)
        .execute_func(module.functions[0].id, vec![])
        .expect("physical enum stack/load operations interpret");
    assert_eq!(outcome.returns, vec![InterpretValue::int(ty, value).expect("fixture fits")]);
}

#[test]
fn physical_enum_aggregate_projection_preserves_payload() {
    let input = fixture(
        Ty::i64(),
        false,
        vec![
            construction(0),
            assign(
                Place::local(0),
                Rvalue::Use(Operand::Copy(Place {
                    local: 1,
                    projections: vec![Projection::Downcast(0), Projection::Field(0)],
                })),
            ),
        ],
    );
    let module = checked(&input);
    assert!(
        instructions(&module)
            .any(|inst| matches!(inst, Inst::ExtractField { ty: IrTy::I64, field: 1, .. }))
    );
    returns(&module, IrTy::I64, 41);
}

#[test]
fn borrowed_physical_enum_discriminant_is_value_not_variant_index() {
    for (variant, expected) in [(0, 11), (1, 37)] {
        let input = fixture(
            Ty::isize(),
            false,
            vec![
                construction(variant),
                borrow(false),
                assign(Place::local(0), Rvalue::Discriminant(dereference())),
            ],
        );
        let module = checked(&input);
        assert!(spells_reference(&module, ProofAnnotation::SharedBorrow));
        assert!(
            instructions(&module).any(|inst| matches!(inst, Inst::Load { ty: IrTy::Enum(_), .. }))
        );
        assert!(
            instructions(&module)
                .any(|inst| matches!(inst, Inst::ExtractField { ty: IrTy::U8, field: 0, .. }))
        );
        returns(&module, IrTy::I64, expected);
    }
}

#[test]
fn borrowed_physical_enum_projection_loads_whole_enum_then_payload() {
    let input = fixture(
        Ty::i64(),
        false,
        vec![
            construction(0),
            borrow(false),
            assign(
                Place::local(0),
                Rvalue::Use(Operand::Copy(Place {
                    local: 2,
                    projections: vec![
                        Projection::Deref,
                        Projection::Downcast(0),
                        Projection::Field(0),
                    ],
                })),
            ),
        ],
    );
    let module = checked(&input);
    assert!(spells_reference(&module, ProofAnnotation::SharedBorrow));
    assert!(instructions(&module).any(|inst| matches!(inst, Inst::Load { ty: IrTy::Enum(_), .. })));
    assert!(
        instructions(&module)
            .any(|inst| matches!(inst, Inst::ExtractField { ty: IrTy::I64, field: 1, .. }))
    );
    returns(&module, IrTy::I64, 41);
}

#[test]
fn borrowed_physical_enum_set_discriminant_replaces_payload_with_fieldless_variant() {
    let input = fixture(
        Ty::isize(),
        true,
        vec![
            construction(0),
            borrow(true),
            Statement::SetDiscriminant { place: dereference(), variant_index: 1 },
            // Read through the original address-taken local, not an SSA copy of
            // the replacement, so a stale stack-cell cache cannot pass this test.
            assign(Place::local(0), Rvalue::Discriminant(Place::local(1))),
        ],
    );
    let module = checked(&input);
    assert!(spells_reference(&module, ProofAnnotation::UniqueBorrow));
    assert!(
        instructions(&module).any(|inst| matches!(inst, Inst::Store { ty: IrTy::Enum(_), .. }))
    );
    assert!(instructions(&module).any(|inst| matches!(inst,
        Inst::Const { ty: IrTy::Enum(_), value: Constant::Aggregate(fields) }
            if fields.as_slice() == [Constant::Int(37)])));
    returns(&module, IrTy::I64, 37);
}

#[test]
fn physical_enum_out_of_range_variant_is_refused_for_read_and_construction() {
    let bad_read = fixture(
        Ty::i64(),
        false,
        vec![
            construction(0),
            assign(
                Place::local(0),
                Rvalue::Use(Operand::Copy(Place {
                    local: 1,
                    projections: vec![Projection::Downcast(2), Projection::Field(0)],
                })),
            ),
        ],
    );
    let error = lower_to_trust_ir(&bad_read).expect_err("out-of-range variant read must refuse");
    assert!(error.to_string().contains("variant 2 out of range"), "{error}");
    let bad_construction = fixture(
        Ty::isize(),
        false,
        vec![construction(2), assign(Place::local(0), Rvalue::Discriminant(Place::local(1)))],
    );
    let error =
        lower_to_trust_ir(&bad_construction).expect_err("out-of-range constructor must refuse");
    assert!(error.to_string().contains("variant index 2 out of range"), "{error}");
}

#[test]
fn physical_enum_payload_set_discriminant_still_requires_staging() {
    let input = fixture(
        Ty::isize(),
        true,
        vec![
            construction(1),
            borrow(true),
            Statement::SetDiscriminant { place: dereference(), variant_index: 0 },
            assign(Place::local(0), Rvalue::Discriminant(Place::local(1))),
        ],
    );
    let error =
        lower_to_trust_ir(&input).expect_err("payload-bearing tag-only write stays unsupported");
    assert!(error.to_string().contains("SetDiscriminant to payload-bearing variant 0"), "{error}");
}

// E2-ZST-INACTIVE-LANE-1 (docs/DECISION_QUEUE.md): a FLAT enum construction (the
// `__tag` + `__v{variant}_{field}` struct view, no faithful repr) whose unwritten
// lanes are all zero-sized is complete, so it is one `MakeAggregate`, which the
// reference interpreter executes. A construction that leaves a lane with bytes (or
// an opaque generic `T`) unwritten keeps the partial poison seed, which it does not.

const FLAT: &str = "synthetic_flat::Maybe";

fn flat_definition(payload: Ty) -> Ty {
    Ty::Adt {
        name: FLAT.into(),
        fields: vec![("__tag".into(), Ty::i64()), ("__v1_0".into(), payload.clone())].into(),
        variants: vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), payload)],
            },
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Enum),
    }
}

/// `fn f() -> i64 { let v = Maybe::None; discriminant(v) }` over the flat view.
fn flat_none_discriminant(payload: Ty) -> VerifiableFunction {
    let definition = flat_definition(payload);
    VerifiableFunction {
        name: "flat_none".into(),
        def_path: "synthetic_flat::flat_none".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: definition.clone(), name: Some("value".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(
                        Place::local(1),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: FLAT.into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![],
                        ),
                    ),
                    assign(Place::local(0), Rvalue::Discriminant(Place::local(1))),
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i64(),
            datatype_defs: [(FLAT.into(), definition)].into(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn flat_lowered(payload: Ty) -> Module {
    let input = flat_none_discriminant(payload);
    let before = input.content_hash();
    let module = lower_to_trust_ir(&input).expect("flat enum construction lowers");
    assert_eq!(input.content_hash(), before);
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "flat enum output must validate: {errors:?}");
    assert!(module.enums.is_empty(), "the flat view is a struct, not a first-class enum");
    module
}

#[test]
fn a_flat_enum_construction_with_only_zero_sized_unwritten_lanes_is_one_complete_constructor() {
    let zero_sized = [
        ("()", Ty::Unit),
        ("empty tuple", Ty::Tuple(vec![])),
        (
            "capture-free closure",
            Ty::Closure {
                name: "synthetic_flat::checker::{closure#0}".into(),
                upvars: vec![],
                call: None,
            },
        ),
    ];
    for (label, payload) in zero_sized {
        let module = flat_lowered(payload);
        assert!(
            !instructions(&module)
                .any(|inst| matches!(inst, Inst::Undef { .. } | Inst::InsertField { .. })),
            "{label}: a complete construction has no poison seed: {:#?}",
            module.functions[0].blocks
        );
        let nodes: Vec<_> =
            module.functions[0].blocks.iter().flat_map(|block| &block.body).collect();
        let constant = |value| {
            nodes.iter().find_map(|node| match (&node.inst, node.results.as_slice()) {
                (Inst::Const { value: v, .. }, [result]) if *v == value => Some(*result),
                _ => None,
            })
        };
        let (Some(tag), Some(unit)) = (constant(Constant::Int(0)), constant(Constant::PhantomData))
        else {
            panic!("{label}: the tag and unit constants are emitted: {nodes:#?}");
        };
        let constructors: Vec<_> = instructions(&module)
            .filter_map(|inst| match inst {
                Inst::MakeAggregate { ty: IrTy::Struct(_), variant: None, fields } => {
                    Some(fields.clone())
                }
                _ => None,
            })
            .collect();
        assert_eq!(constructors, vec![vec![tag, unit]], "{label}: one constructor, lanes in order");
        returns(&module, IrTy::I64, 0);
    }
}

#[test]
fn a_flat_enum_construction_leaving_a_lane_with_bytes_or_an_opaque_generic_unwritten_keeps_the_seed()
 {
    let not_zero_sized = [
        ("i64", Ty::i64()),
        ("generic T", Ty::Unsupported { kind: "TyKind::Param".into(), detail: "T".into() }),
    ];
    for (label, payload) in not_zero_sized {
        let module = flat_lowered(payload);
        assert!(
            instructions(&module).any(|inst| matches!(inst, Inst::Undef { ty: IrTy::Struct(_) })),
            "{label}: a partial construction keeps its seed"
        );
        assert!(
            !instructions(&module).any(|inst| matches!(inst, Inst::MakeAggregate { .. })),
            "{label}: no complete constructor for a partial construction"
        );
        assert!(
            !instructions(&module)
                .any(|inst| matches!(inst, Inst::Const { value: Constant::PhantomData, .. })),
            "{label}: no unwritten lane is filled"
        );
        let outcome =
            Interpreter::with_module(&module).execute_func(module.functions[0].id, vec![]);
        assert!(
            outcome.is_err(),
            "{label}: the reference interpreter refuses the seed: {outcome:?}"
        );
    }
}
