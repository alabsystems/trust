//! Exact integer-cast transition controls. Native casts are a differential
//! oracle, not a universal compiler/refinement certificate.
use super::*;

fn integer(width: u32, signed: bool) -> Ty {
    Ty::Int { width, signed }
}

fn function(source: Ty, target: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "cast".into(),
        def_path: "tests::cast".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: target.clone(), name: Some("out".into()) },
                LocalDecl { index: 1, ty: source, name: Some("input".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Move(Place::local(1)), target.clone()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: target,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn cast(func: &VerifiableFunction, value: Formula) -> Option<Formula> {
    let mut state = initial_symbolic_state(func);
    state.insert("input".into(), value);
    apply_symbolic_statements(func, &func.body.blocks[0], &mut state, None)?;
    state.remove("out")
}

#[derive(Debug, PartialEq)]
enum Value {
    Signed(i128),
    Unsigned(u128),
    Bits(u128, u32),
}

fn mask(width: u32) -> u128 {
    assert!(matches!(width, 8 | 16 | 32 | 64 | 128));
    if width == 128 { u128::MAX } else { (1u128 << width) - 1 }
}

// Small, closed mathematical interpreter for the emitted bridge nodes. The
// expected results below are separate native Rust `as` operations.
fn evaluate(formula: &Formula) -> Value {
    match formula {
        Formula::Int(value) => Value::Signed(*value),
        Formula::UInt(value) => Value::Unsigned(*value),
        Formula::IntToBv(inner, width) => {
            let bits = match evaluate(inner) {
                Value::Signed(value) => value as u128,
                Value::Unsigned(value) => value,
                other => panic!("not an integer: {other:?}"),
            };
            Value::Bits(bits & mask(*width), *width)
        }
        Formula::BvToInt(inner, width, signed) => {
            let Value::Bits(bits, actual_width) = evaluate(inner) else {
                panic!("not a bitvector")
            };
            assert_eq!(*width, actual_width);
            if *signed {
                let sign_bit = 1u128 << (width - 1);
                let extended = if bits & sign_bit != 0 { bits | !mask(*width) } else { bits };
                Value::Signed(extended as i128)
            } else {
                Value::Unsigned(bits)
            }
        }
        other => panic!("cast introduced non-bridge expression: {other:?}"),
    }
}

fn assert_value(source: Ty, target: Ty, input: Formula, expected: Value) {
    let result = cast(&function(source.clone(), target.clone()), input.clone())
        .unwrap_or_else(|| panic!("cast missing: {source:?} -> {target:?}, {input:?}"));
    assert!(formula_has_sort(&result, Sort::Int), "{result:?}");
    assert_eq!(evaluate(&result), expected, "{source:?} -> {target:?}: {input:?}");
}

macro_rules! all_destinations {
    ($value:expr, $source:expr, $input:expr) => {{
        let value = $value;
        macro_rules! unsigned {
            ($ty:ty, $width:expr) => {
                assert_value(
                    $source.clone(),
                    integer($width, false),
                    $input.clone(),
                    Value::Unsigned((value as $ty) as u128),
                );
            };
        }
        macro_rules! signed {
            ($ty:ty, $width:expr) => {
                assert_value(
                    $source.clone(),
                    integer($width, true),
                    $input.clone(),
                    Value::Signed((value as $ty) as i128),
                );
            };
        }
        unsigned!(u8, 8);
        unsigned!(u16, 16);
        unsigned!(u32, 32);
        unsigned!(u64, 64);
        unsigned!(u128, 128);
        signed!(i8, 8);
        signed!(i16, 16);
        signed!(i32, 32);
        signed!(i64, 64);
        signed!(i128, 128);
    }};
}

#[test]
fn unsigned_widening_baseline() {
    assert_value(integer(8, false), integer(32, false), Formula::Int(255), Value::Unsigned(255));
}

#[test]
fn exhaustive_u8_and_i8_against_native_casts() {
    for value in u8::MIN..=u8::MAX {
        all_destinations!(value, integer(8, false), Formula::UInt(value.into()));
    }
    for value in i8::MIN..=i8::MAX {
        all_destinations!(value, integer(8, true), Formula::Int(value.into()));
    }
}

#[test]
fn all_machine_width_boundaries_against_native_casts() {
    macro_rules! boundaries {
        ($ty:ty, $width:expr, false) => {
            for value in [0, 1, <$ty>::MAX / 2, <$ty>::MAX / 2 + 1, <$ty>::MAX - 1, <$ty>::MAX] {
                all_destinations!(
                    value as $ty,
                    integer($width, false),
                    Formula::UInt(value as u128)
                );
            }
        };
        ($ty:ty, $width:expr, true) => {
            for value in [<$ty>::MIN, <$ty>::MIN + 1, -1, 0, 1, <$ty>::MAX] {
                all_destinations!(value as $ty, integer($width, true), Formula::Int(value as i128));
            }
        };
    }
    boundaries!(u8, 8, false);
    boundaries!(u16, 16, false);
    boundaries!(u32, 32, false);
    boundaries!(u64, 64, false);
    boundaries!(u128, 128, false);
    boundaries!(i8, 8, true);
    boundaries!(i16, 16, true);
    boundaries!(i32, 32, true);
    boundaries!(i64, 64, true);
    boundaries!(i128, 128, true);
}

#[test]
fn source_normalization_precedes_target_normalization() {
    // These deliberately non-normal symbolic states distinguish the declared
    // source carrier from an identity cast or target-only truncation.
    assert_value(
        integer(8, true),
        integer(32, false),
        Formula::Int(255),
        Value::Unsigned(u32::MAX.into()),
    );
    assert_value(integer(8, false), integer(32, true), Formula::Int(-1), Value::Signed(255));
    assert_value(integer(8, false), integer(128, false), Formula::UInt(256), Value::Unsigned(0));
    assert_value(integer(16, true), integer(128, true), Formula::UInt(65535), Value::Signed(-1));
}

#[test]
fn source_and_target_carriers_are_independent() {
    let u8_to_i32 =
        cast(&function(integer(8, false), integer(32, true)), Formula::Int(255)).unwrap();
    let i8_to_i32 =
        cast(&function(integer(8, true), integer(32, true)), Formula::Int(255)).unwrap();
    let u8_to_i8 = cast(&function(integer(8, false), integer(8, true)), Formula::Int(255)).unwrap();
    assert_ne!(u8_to_i32, i8_to_i32);
    assert_ne!(u8_to_i32, u8_to_i8);
    assert_eq!(evaluate(&u8_to_i32), Value::Signed(255));
    assert_eq!(evaluate(&i8_to_i32), Value::Signed(-1));
    assert_eq!(evaluate(&u8_to_i8), Value::Signed(-1));
}

#[test]
fn pinned_pointer_sized_integer_carrier_is_64_not_a_pointer_cast() {
    assert_eq!(usize::BITS, 64, "fixture's pinned target boundary");
    assert_value(
        Ty::PtrSizedInt { signed: true },
        integer(128, false),
        Formula::Int(-1),
        Value::Unsigned(u128::MAX),
    );
    assert_value(
        integer(128, false),
        Ty::PtrSizedInt { signed: false },
        Formula::UInt(u128::MAX),
        Value::Unsigned(u64::MAX.into()),
    );
}

#[test]
fn signed_width_erased_and_other_ambiguous_operands_refuse() {
    let func = function(integer(8, false), integer(32, false));
    for operand in [
        Operand::Constant(ConstValue::Int(-1)),
        Operand::Constant(ConstValue::Bool(true)),
        Operand::Constant(ConstValue::Uint(256, 8)),
        Operand::Constant(ConstValue::Uint(1, 7)),
        Operand::Constant(ConstValue::ConstParam {
            index: 0,
            name: "N".into(),
            width: 8,
            signed: false,
        }),
        Operand::Constant(ConstValue::opaque_scalar(8, false)),
        Operand::Symbolic(Formula::Int(1)),
        Operand::Copy(Place::local(99)),
    ] {
        assert!(
            symbolic_rvalue(
                &func,
                &Rvalue::Cast(operand.clone(), integer(32, false)),
                &initial_symbolic_state(&func),
                None
            )
            .is_none(),
            "{operand:?}"
        );
    }
}

#[test]
fn typed_unsigned_constants_keep_exact_width_and_full_u128_value() {
    let func = function(integer(8, false), integer(128, true));
    for (value, width, expected) in [(255, 8, 255), (u128::MAX, 128, -1)] {
        let result = symbolic_rvalue(
            &func,
            &Rvalue::Cast(Operand::Constant(ConstValue::Uint(value, width)), integer(128, true)),
            &initial_symbolic_state(&func),
            None,
        )
        .unwrap();
        assert_eq!(evaluate(&result), Value::Signed(expected));
    }
}

#[test]
fn unsupported_types_and_bad_state_sorts_refuse() {
    let unsupported = [
        Ty::Bool,
        Ty::Char,
        Ty::Unit,
        Ty::Float { width: 32 },
        Ty::Float { width: 64 },
        integer(0, false),
        integer(7, true),
        integer(256, false),
        Ty::Ref { mutable: false, inner: Box::new(integer(8, false)) },
    ];
    for ty in unsupported {
        assert!(
            cast(&function(ty.clone(), integer(32, false)), Formula::Int(1)).is_none(),
            "source {ty:?}"
        );
        assert!(
            cast(&function(integer(8, false), ty.clone()), Formula::Int(1)).is_none(),
            "target {ty:?}"
        );
    }
    for bad in [
        Formula::Bool(true),
        Formula::BitVec { value: 1, width: 8 },
        Formula::IntToBv(Box::new(Formula::Bool(false)), 8),
    ] {
        assert!(cast(&function(integer(8, false), integer(32, false)), bad).is_none());
    }
}

#[test]
fn noncanonical_or_mismatched_local_identity_refuses_without_assignment() {
    for mutation in 0..5 {
        let mut func = function(integer(8, false), integer(32, false));
        match mutation {
            0 => func.body.locals[0].ty = integer(16, false),
            1 => func.body.locals[0].index = 7,
            2 => func.body.locals[1].index = 7,
            3 => {
                let Statement::Assign { place, .. } = &mut func.body.blocks[0].stmts[0] else {
                    unreachable!()
                };
                *place = Place::local(99);
            }
            _ => func.body.locals.push(func.body.locals[1].clone()),
        }
        let mut state = initial_symbolic_state(&func);
        let before = state.clone();
        assert!(
            apply_symbolic_statements(&func, &func.body.blocks[0], &mut state, None).is_none(),
            "mutation {mutation}"
        );
        assert_eq!(state, before, "a refused cast must not install a value");
    }
}

#[test]
fn shadowed_source_names_keep_distinct_canonical_state_slots() {
    let mut func = function(integer(8, true), integer(32, false));
    func.body.locals[0].name = Some("input".into());
    let source = crate::place_to_var_name(&func, &Place::local(1));
    let dest = crate::place_to_var_name(&func, &Place::local(0));
    assert_ne!(source, dest);
    let mut state = initial_symbolic_state(&func);
    state.insert(source.clone(), Formula::Int(-1));
    state.insert(dest.clone(), Formula::Int(7));
    apply_symbolic_statements(&func, &func.body.blocks[0], &mut state, None).unwrap();
    assert_eq!(evaluate(&state[&dest]), Value::Unsigned(u32::MAX.into()));
    assert_eq!(state[&source], Formula::Int(-1));
}

#[test]
fn rhs_snapshot_survives_same_local_write_and_invalidates_old_projections() {
    let mut func = function(integer(8, false), integer(8, false));
    let Statement::Assign { place, .. } = &mut func.body.blocks[0].stmts[0] else { unreachable!() };
    *place = Place::local(1);
    let mut state = initial_symbolic_state(&func);
    state.insert("input".into(), Formula::UInt(255));
    state.insert("input.0".into(), Formula::Int(17));
    state.insert("out".into(), Formula::Int(12));
    apply_symbolic_statements(&func, &func.body.blocks[0], &mut state, None).unwrap();
    assert_eq!(evaluate(&state["input"]), Value::Unsigned(255));
    assert!(!state.contains_key("input.0"));
    assert_eq!(state["out"], Formula::Int(12));
}

#[test]
fn projections_are_not_admitted_from_their_final_integer_type_alone() {
    let mut func = function(Ty::Tuple(vec![integer(8, false)]), integer(32, false));
    let operand = Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] });
    assert_eq!(crate::operand_ty_cow(&func, &operand).as_deref(), Some(&integer(8, false)));
    assert!(
        symbolic_rvalue(
            &func,
            &Rvalue::Cast(operand, integer(32, false)),
            &initial_symbolic_state(&func),
            None
        )
        .is_none()
    );
    func.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(integer(8, false)) };
    let operand = Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] });
    assert_eq!(crate::operand_ty_cow(&func, &operand).as_deref(), Some(&integer(8, false)));
    assert!(
        symbolic_rvalue(
            &func,
            &Rvalue::Cast(operand, integer(32, false)),
            &initial_symbolic_state(&func),
            None
        )
        .is_none()
    );
}

#[test]
fn substitution_uses_exact_source_snapshot_without_recursing_into_destination() {
    let func = function(integer(8, true), integer(32, false));
    let mut state = initial_symbolic_state(&func);
    state.insert("input".into(), Formula::Var("out".into(), Sort::Int));
    state.insert("out".into(), Formula::Int(7));
    apply_symbolic_statements(&func, &func.body.blocks[0], &mut state, None).unwrap();
    assert_eq!(
        state["out"],
        Formula::BvToInt(
            Box::new(Formula::IntToBv(
                Box::new(Formula::BvToInt(
                    Box::new(Formula::IntToBv(Box::new(Formula::Var("out".into(), Sort::Int)), 8)),
                    8,
                    true
                )),
                32
            )),
            32,
            false
        )
    );
    assert_eq!(state["input"], Formula::Var("out".into(), Sort::Int));
}

#[test]
fn mixed_machine_domain_translation_is_not_relaxed_by_cast_support() {
    let func = function(integer(8, false), integer(32, false));
    let encoded = cast(&func, Formula::Var("input".into(), Sort::Int)).unwrap();
    assert!(formula_contains_machine_encoding(&encoded));
    assert!(
        machine_faithful_vc_formula(
            &func,
            &Formula::Eq(Box::new(encoded), Box::new(Formula::Var("out".into(), Sort::Int)))
        )
        .is_none()
    );
}

#[test]
#[ignore = "requires explicitly bound actual compiler A10 extract"]
fn actual_a10_cast_statement_advances_without_claiming_loop_completion() {
    let path =
        std::env::var("TRUST_INTEGER_CAST_A10_INPUT").expect("explicit retained input required");
    let bytes = std::fs::read(&path).unwrap();
    let func: VerifiableFunction = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(func.def_path, "a10_saturating_fold::saturating_fold");
    assert_eq!(func.body.locals[10].ty, integer(8, false));
    assert_eq!(func.body.locals[9].ty, integer(32, false));
    let block = &func.body.blocks[3];
    assert_eq!(block.stmts.len(), 2);
    assert!(
        matches!(&block.stmts[1], Statement::Assign { place, rvalue: Rvalue::Cast(Operand::Move(source), target), .. } if *place == Place::local(9) && *source == Place::local(10) && *target == integer(32, false))
    );
    let mut state = initial_symbolic_state(&func);
    apply_symbolic_statements(&func, block, &mut state, None)
        .expect("both actual bb3 statements now have exact denotations");
    let output = &state[&crate::place_to_var_name(&func, &Place::local(9))];
    let source = state[&crate::place_to_var_name(&func, &Place::local(10))].clone();
    assert!(matches!(&source, Formula::Select(..)), "the real source collection read must survive");
    assert_eq!(
        *output,
        Formula::BvToInt(
            Box::new(Formula::IntToBv(
                Box::new(Formula::BvToInt(
                    Box::new(Formula::IntToBv(Box::new(source), 8)),
                    8,
                    false
                )),
                32
            )),
            32,
            false
        )
    );
    assert!(formula_contains_machine_encoding(output));
    assert!(formula_has_sort(output, Sort::Int));
    let transitions = symbolic_loop_transitions(&func, BlockId(1));
    println!("actual A10 transition result: {transitions:?}");
    let transitions = transitions.expect("cast no longer blocks this exact transition");
    assert_eq!(transitions.len(), 1);
    assert_eq!(
        transitions[0].post_state["acc"],
        Formula::Var("_7#e45_call_bb3".into(), Sort::Int),
        "existing call-result havoc remains; this is NOT a saturating_add model"
    );
    let mut vcs = Vec::new();
    check_contracts(&func, &mut vcs);
    let gaps: Vec<_> = vcs
        .iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { detail, .. } => Some(detail),
            _ => None,
        })
        .collect();
    println!("actual A10 remaining public contract gaps: {gaps:?}");
    assert!(gaps.is_empty(), "the exact local transition now produces ordinary E4/E5 candidates");
    assert_eq!(
        vcs.iter()
            .filter(|vc| matches!(
                vc.kind,
                VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
            ))
            .count(),
        2
    );
    assert!(
        vcs.iter().any(|vc| machine_faithful_vc_formula(&func, &vc.formula).is_none()),
        "the unchanged full machine-domain translator still refuses collection/mixed-width formulas"
    );
    assert_eq!(std::fs::read(path).unwrap(), bytes);
}
