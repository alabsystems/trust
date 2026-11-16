//! Execute the complete, unmodified producer module against a Rust test oracle.
//! Empirical regression evidence only: no host model, proof or admission claim.
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::{Module, Ty};

#[path = "../../../../../tests/run-make/trust-array-reference-place/indexed_field_compound_assign.rs"]
mod oracle;

fn execute(module: &Module, name: &str, args: &[u64]) -> Result<u64, InterpretErrorCode> {
    let functions: Vec<_> = module.functions.iter().filter(|function| {
        function.display_path.as_deref().unwrap_or(&function.name).rsplit("::").next() == Some(name)
    }).collect();
    assert_eq!(functions.len(), 1, "one unique original function: {name}");
    let function = functions[0];
    let signature = &module.func_types[function.ty.as_usize()];
    assert_eq!(signature.params, vec![Ty::U64; args.len()]);
    assert_eq!(signature.returns, vec![Ty::U64]);
    let values = args.iter().map(|value| InterpretValue::int(Ty::U64, i128::from(*value)).unwrap());
    let result = Interpreter::with_module(module).execute_func(function.id, values)
        .map_err(|error| error.code)?;
    assert_eq!(result.host_calls, 0, "no host-supplied executable semantics");
    assert!(result.steps > 0);
    assert_eq!(result.returns.len(), 1);
    assert_eq!(result.returns[0].ty, Ty::U64);
    Ok(u64::try_from(result.returns[0].as_int().unwrap().as_unsigned()).unwrap())
}

fn check(module: &Module, name: &str, args: &[u64], oracle: impl FnOnce() -> u64)
    -> bool
{
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let expected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(oracle));
    std::panic::set_hook(hook);
    let actual = execute(module, name, args);
    match (expected, actual) {
        (Ok(expected), Ok(actual)) => {
            assert_eq!(actual, expected, "original {name}({args:?})");
            false
        }
        (Err(_), Err(InterpretErrorCode::Panic)) => true,
        (expected, actual) => panic!("original {name}({args:?}): oracle={expected:?}, trust-ir={actual:?}"),
    }
}

fn main() {
    let path = std::env::args().nth(1).expect("actual complete compiler module path");
    let bytes = std::fs::read(path).unwrap();
    let module = trust_ir::binary::deserialize_module(&bytes).expect("decode actual producer bytes");
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes,
        "complete canonical module, without projecting or rewriting any body");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "complete original module validation: {errors:?}");
    // Expected Rust panics are counted and compared with the interpreter's
    // precise Panic code. Unsupported/UB/fuel errors must never count as agreement.
    let mut cases = 0;
    let mut panics = 0;
    let zero: [(&str, fn() -> u64); 8] = [
        ("compound_effect_order", oracle::compound_effect_order),
        ("compound_rhs_replaces_array", oracle::compound_rhs_replaces_array),
        ("compound_index_replaces_array", oracle::compound_index_replaces_array),
        ("compound_nested", oracle::compound_nested),
        ("compound_loop", oracle::compound_loop),
        ("compound_float", oracle::compound_float),
        ("compound_rhs_return_before_bounds", oracle::compound_rhs_return_before_bounds),
        ("compound_index_return_after_rhs", oracle::compound_index_return_after_rhs),
    ];
    for (name, oracle) in zero {
        panics += usize::from(check(&module, name, &[], oracle));
        cases += 1;
    }
    let parameterized: [(&str, fn(u64) -> u64); 8] = [
        ("compound_mixed_shift", oracle::compound_mixed_shift),
        ("compound_bounds", oracle::compound_bounds),
        ("compound_checked_add", oracle::compound_checked_add),
        ("compound_divisor", oracle::compound_divisor),
        ("compound_signed_divisor", oracle::compound_signed_divisor),
        ("compound_bit_ops", oracle::compound_bit_ops),
        ("compound_sub_mul_rem", oracle::compound_sub_mul_rem),
        ("compound_nested_sibling_refused", oracle::compound_nested_sibling_refused),
    ];
    let boundaries = [0, 1, 2, 3, 7, 16, 17, 31, 32, 63, 64, 65, 255,
        (1 << 32) - 1, 1 << 32, (1 << 63) - 1, 1 << 63, u64::MAX - 1, u64::MAX];
    for (name, oracle) in parameterized {
        for value in boundaries {
            panics += usize::from(check(&module, name, &[value], || oracle(value)));
            cases += 1;
        }
    }
    assert_eq!(cases, 160, "all original cases plus the newly admitted nested sibling");
    assert!(panics > 0, "bounds, overflow, zero division and signed MIN/-1 are exercised");
    println!("ORIGINAL_COMPOUND_MODULE: {cases} actual cases passed, including {panics} matching panics; empirical only");
}
