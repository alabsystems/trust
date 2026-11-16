//! Synthetic boundary controls only. Compiler identity/impl admission is tested
//! separately by the real rustc-private source harness, never fabricated here.

use trust_types::{BasicBlock, LocalDecl, SourceSpan, UnwindEdge, VerifiableBody};

use super::*;
use crate::{PrimitiveDecimalStringTable, VcgenContext, primitive_decimal_max_bytes};

fn string_ty() -> Ty {
    Ty::adt("alloc::string::String", vec![])
}
fn shared(ty: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(ty) }
}
fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}
fn call(name: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: name.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(name),
        unwind: UnwindEdge::Unreachable,
    }
}
fn fixture() -> VerifiableFunction {
    let types = [
        Ty::Unit,
        Ty::u64(),
        shared(Ty::u64()),
        string_ty(),
        shared(string_ty()),
        Ty::u64(),
        Ty::u64(),
    ];
    let mut func = VerifiableFunction {
        name: "decimal".into(),
        def_path: "fixture::decimal".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: types
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(2, Rvalue::Ref { mutable: false, place: Place::local(1) })],
                    terminator: call(
                        "alloc::string::ToString::to_string",
                        vec![Operand::Copy(Place::local(2))],
                        3,
                        1,
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(4, Rvalue::Ref { mutable: false, place: Place::local(3) })],
                    terminator: call(
                        "alloc::string::String::len",
                        vec![Operand::Copy(Place::local(4))],
                        5,
                        2,
                    ),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        6,
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(5)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ),
                    )],
                    terminator: Terminator::Drop {
                        place: Place::local(3),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    // The old sep-engine spelling fixture map predates StringLen. Supply this
    // synthetic key from the real typed declaration registry, never as producer
    // or real-frontend credit.
    if let Terminator::Call { callee_key, .. } = &mut func.body.blocks[1].terminator {
        let key = callee_key.as_mut().unwrap();
        key.sysroot_item = trust_types::callee_key::sysroot_item_for(
            "alloc",
            trust_types::CalleeOwner::Inherent(trust_types::SelfTyHead::Adt("String")),
            "len",
        );
        assert_eq!(key.sysroot_item, Some(trust_types::SysrootItem::StringLen));
        key.krate_is_real_sysroot = true;
    }
    func
}
fn table(func: &VerifiableFunction) -> PrimitiveDecimalStringTable {
    let mut table = PrimitiveDecimalStringTable::for_function(func);
    table.record_authenticated_call(BlockId(0), &func.body.blocks[0].terminator, Ty::u64(), true);
    table
}
fn facts(func: &VerifiableFunction, context: &VcgenContext) -> FxHashMap<BlockId, Vec<Formula>> {
    crate::with_function_vcgen_context(&func.def_path, context, || {
        super::primitive_decimal_len::build_primitive_decimal_len_guard_map(func)
    })
}
fn embedded_facts(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    facts(
        func,
        &VcgenContext::for_function(func.def_path.clone())
            .with_primitive_decimal_strings(table(func), func),
    )
}

#[test]
fn primitive_decimal_widths_and_native_extrema_agree() {
    macro_rules! integer {
        ($t:ty, $width:expr, $signed:expr, $maximum:expr) => {{
            let bound =
                primitive_decimal_max_bytes(&Ty::Int { width: $width, signed: $signed }).unwrap();
            assert_eq!(bound, $maximum);
            for value in [<$t>::MIN, 0, 1, <$t>::MAX] {
                assert!(value.to_string().len() <= usize::from(bound));
            }
        }};
    }
    integer!(u8, 8, false, 3);
    integer!(u16, 16, false, 5);
    integer!(u32, 32, false, 10);
    integer!(u64, 64, false, 20);
    integer!(u128, 128, false, 39);
    integer!(i8, 8, true, 4);
    integer!(i16, 16, true, 6);
    integer!(i32, 32, true, 11);
    integer!(i64, 64, true, 20);
    integer!(i128, 128, true, 40);
    for ty in [
        Ty::Bool,
        Ty::Char,
        Ty::f64_ty(),
        shared(Ty::u64()),
        string_ty(),
        Ty::Int { width: 7, signed: false },
    ] {
        assert_eq!(primitive_decimal_max_bytes(&ty), None);
    }
}

#[test]
fn primitive_decimal_fact_requires_live_authority_and_preserves_model_identity() {
    let func = fixture();
    let before = trust_types::stable_model_json_bytes(&func).unwrap();
    assert!(facts(&func, &VcgenContext::for_function(func.def_path.clone())).is_empty());
    assert_eq!(table(&func).max_bytes_at(&func, BlockId(0)), Some(20));
    assert!(
        super::iterator_yield::payload_carries_global_fact(&func, 5),
        "numeric return is single-valued"
    );
    assert_eq!(
        super::primitive_decimal_len::decimal_string_origin(&func, 4, 16),
        Some(BlockId(0)),
        "shared String value traces to its exact admitted call"
    );
    let owned_context = VcgenContext::for_function(func.def_path.clone())
        .with_primitive_decimal_strings(table(&func), &func);
    crate::with_function_vcgen_context(&func.def_path, &owned_context, || {
        assert!(
            crate::compiler_primitive_decimal_strings(&func).is_some(),
            "the unchanged owner/body retains its installed table"
        );
    });
    let bound = embedded_facts(&func);
    assert!(bound.get(&BlockId(2)).is_some_and(|rows| {
        rows.iter().any(|row| matches!(row, Formula::Le(_, upper) if **upper == Formula::Int(20)))
    }));
    assert_eq!(trust_types::stable_model_json_bytes(&func).unwrap(), before);
    let decoded: VerifiableFunction = serde_json::from_slice(&before).unwrap();
    assert!(facts(&decoded, &VcgenContext::for_function(decoded.def_path.clone())).is_empty());
    let foreign = VcgenContext::for_function("other::function")
        .with_primitive_decimal_strings(table(&func), &func);
    assert!(facts(&func, &foreign).is_empty());
    let mut renamed = func.clone();
    renamed.def_path = "other::same_body".into();
    let rebound = VcgenContext::for_function(renamed.def_path.clone())
        .with_primitive_decimal_strings(table(&func), &renamed);
    assert!(facts(&renamed, &rebound).is_empty(), "identical body cannot change authority owner");
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_primitive_decimal_strings(table(&func), &func);
    let mut changed = func.clone();
    changed.body.blocks[2]
        .stmts
        .push(assign(6, Rvalue::Use(Operand::Constant(ConstValue::Uint(200, 64)))));
    assert!(
        facts(&changed, &context).is_empty(),
        "same-name changed body cannot borrow prior authority"
    );
}

#[test]
fn primitive_decimal_refuses_mismatched_call_receiver_and_duplicate_authority() {
    let func = fixture();
    let mut unfrozen = PrimitiveDecimalStringTable::for_function(&func);
    unfrozen.record_authenticated_call(
        BlockId(0),
        &func.body.blocks[0].terminator,
        Ty::u64(),
        false,
    );
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_primitive_decimal_strings(unfrozen, &func);
    assert!(
        facts(&func, &context).is_empty(),
        "opaque shared borrow needs compiler Freeze license"
    );
    let mut duplicate = table(&func);
    duplicate.record_authenticated_call(
        BlockId(0),
        &func.body.blocks[0].terminator,
        Ty::u64(),
        true,
    );
    let context = VcgenContext::for_function(func.def_path.clone())
        .with_primitive_decimal_strings(duplicate, &func);
    assert!(facts(&func, &context).is_empty());
    for variant in 0..5 {
        let mut changed = func.clone();
        match variant {
            0 => {
                if let Terminator::Call { is_foreign, .. } = &mut changed.body.blocks[0].terminator
                {
                    *is_foreign = true;
                }
            }
            1 => {
                if let Terminator::Call { is_unsafe_sig, .. } =
                    &mut changed.body.blocks[0].terminator
                {
                    *is_unsafe_sig = true;
                }
            }
            2 => changed.body.locals[2].ty = shared(shared(Ty::u64())),
            3 => changed.body.locals[2].ty = shared(Ty::f64_ty()),
            4 => {
                if let Terminator::Call { callee_key, .. } = &mut changed.body.blocks[1].terminator
                {
                    *callee_key = None;
                }
            }
            _ => unreachable!(),
        }
        assert!(embedded_facts(&changed).is_empty(), "variant {variant}");
    }
}

#[test]
fn primitive_decimal_refuses_heap_alias_mutation_and_numeric_reassignment() {
    for variant in 0..5 {
        let mut func = fixture();
        match variant {
            0 => {
                let local = func.body.locals.len();
                func.body.locals.push(LocalDecl {
                    index: local,
                    ty: Ty::Ref { mutable: true, inner: Box::new(string_ty()) },
                    name: None,
                });
                // Direct push_str and mutation through a saved &mut alias both
                // cross this same complete Escape channel on the String itself.
                func.body.blocks[1]
                    .stmts
                    .push(assign(local, Rvalue::Ref { mutable: true, place: Place::local(3) }));
            }
            1 => func.body.blocks[1].stmts.push(assign(
                3,
                Rvalue::Use(Operand::Symbolic(Formula::var("replacement_string", Sort::Int))),
            )),
            2 => func.body.blocks[2]
                .stmts
                .push(assign(5, Rvalue::Use(Operand::Constant(ConstValue::Uint(1_000_000, 64))))),
            3 => func.body.blocks[1].stmts.push(Statement::Deinit { place: Place::local(3) }),
            4 => {
                func.body.blocks[1].stmts.push(assign(6, Rvalue::AddressOf(false, Place::local(3))))
            }
            _ => unreachable!(),
        }
        assert!(embedded_facts(&func).is_empty(), "mutation variant {variant}");
    }
}
