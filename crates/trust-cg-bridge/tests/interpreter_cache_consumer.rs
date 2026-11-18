//! Root compiler-consumer checks for the published immutable interpreter cache.
//! These execute public IR APIs through a workspace member; no proof grade is inferred.
use std::cell::Cell;

use trust_ir::interpret::{InterpreterModule, PanicStrategy};
use trust_ir::signature_abi::*;
use trust_ir::*;

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}
fn f(index: u32) -> FuncId {
    FuncId::new(index)
}
fn b() -> BlockId {
    BlockId::new(0)
}
fn void(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}
fn integer(ty: Ty, n: i128) -> InterpretValue {
    InterpretValue::int(ty, n).unwrap()
}
fn descriptor(arguments: Vec<AbiArgument>, result: AbiArgument) -> SignatureAbi {
    SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-p:64:64-i64:64-i128:128".into(),
            abi: "darwinpcs".into(),
            cpu: "reference-model-test".into(),
            features: vec![],
            target_spec: "model-data-only".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "typed-abi-model-test".into(),
            revision: "not-a-compiler-capture".into(),
        },
        convention: "C".into(),
        lowered_convention: trust_ir::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: arguments.len() as u32,
        arguments,
        result,
    }
}
fn direct(
    place: AbiBindingPlace,
    source: u64,
    carrier: u64,
    bits: u16,
    extension: AbiExtension,
) -> AbiArgument {
    AbiArgument {
        size: source,
        align: 1,
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister { class: AbiRegisterClass::Integer, bytes: carrier },
            source_offset: 0,
            source_bytes: source,
            value_bits: bits,
            attributes: AbiAttributes { extension, ..Default::default() },
        }),
        bindings: vec![AbiBinding {
            place,
            source_offset: 0,
            source_bytes: source,
            carrier_offset: 0,
            carrier_bytes: carrier,
        }],
    }
}
fn module(signature: FuncTy, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("typed-abi-operational-model");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let params = signature.params.clone();
    module.func_types.push(signature);
    let mut function = Function::new(f(0), "entry", FuncTyId::new(0), b());
    let mut block = Block::new(b());
    block.params = params.into_iter().enumerate().map(|(i, ty)| (v(i as u32), ty)).collect();
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
    module
}
fn identity(ty: Ty, bytes: u64, bits: u16) -> Module {
    module(
        FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty],
            is_vararg: false,
            abi: Some(descriptor(
                vec![direct(AbiBindingPlace::Parameter(0), bytes, bytes, bits, AbiExtension::None)],
                direct(AbiBindingPlace::Result(0), bytes, bytes, bits, AbiExtension::None),
            )),
        },
        vec![void(Inst::Return { values: vec![v(0)] })],
    )
}

fn tracked(
    value: InterpretValue,
    consumed: &Cell<usize>,
) -> impl Iterator<Item = InterpretValue> + '_ {
    std::iter::once(value).inspect(|_| consumed.set(consumed.get() + 1))
}

#[test]
fn compiler_consumer_cached_entries_preserve_exact_results_and_run_state() {
    for (ty, bytes, bits) in [(Ty::I32, 4, 32), (Ty::Bool, 1, 1)] {
        let module = identity(ty.clone(), bytes, bits);
        let owner = InterpreterModule::new(&module);
        for n in [0, 1, 0, 1] {
            let value =
                if ty == Ty::Bool { InterpretValue::bool(n != 0) } else { integer(ty.clone(), n) };
            let cached = owner.interpreter().execute_func(f(0), [value.clone()]).unwrap();
            let fresh =
                Interpreter::with_module(&module).execute_func(f(0), [value.clone()]).unwrap();
            assert_eq!(cached, fresh);
            assert_eq!(cached.returns, vec![value]);
            assert_eq!(cached.steps, 1);
            assert_eq!(cached.host_calls, 0);
        }
    }
}

#[test]
fn compiler_consumer_cache_keeps_module_and_current_call_refusals_separate() {
    let valid = identity(Ty::I32, 4, 32);
    let mut invalid = valid.clone();
    invalid.types.push(Ty::Storage(StorageLayout::new(3, 2)));
    let good = InterpreterModule::new(&valid);
    let bad = InterpreterModule::new(&invalid);
    for invalid_module in [false, true, false, true] {
        let (module, owner) = if invalid_module { (&invalid, &bad) } else { (&valid, &good) };
        let consumed = Cell::new(0);
        let cached =
            owner.interpreter().execute_func(f(0), tracked(integer(Ty::I32, 19), &consumed));
        let fresh = Interpreter::with_module(module).execute_func(f(0), [integer(Ty::I32, 19)]);
        assert_eq!(cached, fresh);
        assert_eq!(consumed.get(), usize::from(!invalid_module));
        assert_eq!(cached.is_ok(), !invalid_module);
    }
    for (module, owner) in [(&valid, &good), (&invalid, &bad)] {
        let consumed = Cell::new(0);
        let options =
            InterpretOptions { panic_strategy: PanicStrategy::Unwind, ..Default::default() };
        let cached = owner
            .interpreter()
            .with_options(options)
            .execute_func(f(0), tracked(integer(Ty::I32, 20), &consumed))
            .unwrap_err();
        let fresh = Interpreter::with_module(module)
            .with_options(options)
            .execute_func(f(0), [integer(Ty::I32, 20)])
            .unwrap_err();
        assert_eq!(cached, fresh);
        assert_eq!(cached.code, InterpretErrorCode::UnsupportedCall);
        assert_eq!(cached.block, Some(b()));
        assert_eq!(consumed.get(), 0);
    }
    assert_eq!(
        good.interpreter().execute_func(f(0), [integer(Ty::I32, 21)]).unwrap().returns,
        vec![integer(Ty::I32, 21)]
    );
}
