//! Complete original Unit-effect module, compared with independently compiled Rust.
use std::collections::BTreeSet;
use trust_ir::{Inst, Module, Ty};
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
#[path = "../../../../../tests/run-make/trust-primitive-unit-transport/subject.rs"]
mod oracle;
fn int(value: i32) -> InterpretValue {
    InterpretValue::int_at(Ty::I32, i128::from(value), usize::BITS).unwrap()
}
fn unit() -> InterpretValue {
    InterpretValue { ty: Ty::Unit, kind: InterpretValueKind::Unit }
}
fn tuple(values: Vec<InterpretValue>) -> InterpretValue {
    InterpretValue { ty: Ty::Tuple(values.iter().map(|v| v.ty.clone()).collect()),
        kind: InterpretValueKind::Aggregate(values) }
}
fn short(function: &trust_ir::Function) -> &str {
    function.display_path.as_deref().unwrap_or(&function.name).rsplit("::").next().unwrap()
}
fn check(module: &Module, name: &str, args: Vec<InterpretValue>, expected: InterpretValue) {
    let functions: Vec<_> = module.functions.iter().filter(|f| short(f) == name).collect();
    assert_eq!(functions.len(), 1);
    let function = functions[0];
    assert!(!function.blocks.is_empty());
    let signature = &module.func_types[function.ty.as_usize()];
    assert_eq!(signature.params, args.iter().map(|v| v.ty.clone()).collect::<Vec<_>>());
    assert_eq!(signature.returns, vec![expected.ty.clone()]);
    let result = Interpreter::with_module(module).execute_func(function.id, args)
        .unwrap_or_else(|error| panic!("{name}: {error:?}"));
    assert_eq!(result.host_calls, 0);
    assert!(result.steps > 0);
    assert_eq!(result.returns, vec![expected], "exact Rust effects/result for {name}");
}
fn main() {
    let bytes = std::fs::read(std::env::args().nth(1).expect("complete actual compiler module")).unwrap();
    let module = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes,
        "whole unchanged original module, no projections or replacements");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(module.target_info.as_ref().unwrap().pointer_size * 8, usize::BITS);
    assert_eq!(module.functions.len(), 4);
    let names: BTreeSet<_> = module.functions.iter().map(short).collect();
    assert_eq!(names, BTreeSet::from(["tick", "unit_call_once", "unit_call_after_branch", "unit_tuple_field"]));
    let tick: Vec<_> = module.functions.iter().filter(|f| short(f) == "tick").collect();
    assert_eq!(tick.len(), 1);
    assert!(module.func_types[tick[0].ty.as_usize()].returns.is_empty(), "canonical zero-result Unit call");
    for name in ["unit_call_once", "unit_call_after_branch"] {
        let function = module.functions.iter().find(|f| short(f) == name).unwrap();
        let calls = function.blocks.iter().flat_map(|b| &b.body).filter(|node|
            matches!(&node.inst, Inst::Call { callee, .. } if *callee == tick[0].id)).count();
        assert_eq!(calls, 1, "the actual effectful call must be retained exactly once");
    }
    let delayed = module.functions.iter().find(|f| short(f) == "unit_call_after_branch").unwrap();
    let homes: Vec<_> = delayed.blocks.iter().flat_map(|b| &b.body).filter_map(|node| {
        if matches!(&node.inst, Inst::Alloca { ty: Ty::Unit, .. }) {
            assert_eq!(node.results.len(), 1);
            Some(node.results[0])
        } else { None }
    }).collect();
    assert_eq!(homes.len(), 1);
    let entry = delayed.blocks.iter().find(|b| b.id == delayed.entry).unwrap();
    assert!(!entry.body.iter().any(|node|
        matches!(&node.inst, Inst::Store { ptr, .. } if *ptr == homes[0])),
        "no Unit initializer before the actual source branch");
    assert_eq!(delayed.blocks.iter().flat_map(|b| &b.body).filter(|node|
        matches!(&node.inst, Inst::Store { ptr, ty: Ty::Unit, .. } if *ptr == homes[0])).count(),
        3, "two literal branch assignments and the completed Unit-call value");
    let mut cases = 0;
    for start in [-9, 0, 7, i32::MAX - 1] {
        let expected = oracle::unit_call_once(start, ((),));
        check(&module, "unit_call_once", vec![int(start), tuple(vec![unit()])],
            tuple(vec![int(expected.0), unit()]));
        cases += 1;
        for flag in [false, true] {
            let expected = oracle::unit_call_after_branch(start, flag);
            check(&module, "unit_call_after_branch", vec![int(start), InterpretValue::bool(flag)],
                tuple(vec![int(expected.0), unit()]));
            cases += 1;
        }
        let expected = oracle::unit_tuple_field((), start);
        check(&module, "unit_tuple_field", vec![unit(), int(start)], tuple(vec![unit(), int(expected.1)]));
        cases += 1;
    }
    assert_eq!(cases, 16);
    println!("ORIGINAL_UNIT_TRANSPORT_MODULE: 16 effect-and-value cases; empirical only");
}
