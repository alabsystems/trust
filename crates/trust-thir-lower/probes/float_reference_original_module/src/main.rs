//! Execute the complete producer module against independently compiled Rust.
//! Raw IEEE bits distinguish signed zero and NaN payloads without float equality.
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{Module, Ty};

#[path = "../../../../../tests/run-make/trust-float-reference-storage/subject.rs"]
mod oracle;

fn float32(bits: u32) -> InterpretValue {
    InterpretValue { ty: Ty::F32, kind: InterpretValueKind::FloatBits(u64::from(bits)) }
}

fn float64(bits: u64) -> InterpretValue {
    InterpretValue { ty: Ty::F64, kind: InterpretValueKind::FloatBits(bits) }
}

fn boolean(value: bool) -> InterpretValue {
    InterpretValue { ty: Ty::Bool, kind: InterpretValueKind::Bool(value) }
}

fn check(module: &Module, name: &str, args: Vec<InterpretValue>, ty: Ty, expected: u64) {
    let functions: Vec<_> = module.functions.iter().filter(|function| {
        function.display_path.as_deref().unwrap_or(&function.name).rsplit("::").next() == Some(name)
    }).collect();
    assert_eq!(functions.len(), 1, "one unique original function: {name}");
    let function = functions[0];
    let signature = &module.func_types[function.ty.as_usize()];
    assert_eq!(signature.params, args.iter().map(|value| value.ty.clone()).collect::<Vec<_>>());
    assert_eq!(signature.returns, vec![ty.clone()]);
    let result = Interpreter::with_module(module).execute_func(function.id, args)
        .unwrap_or_else(|error| panic!("original {name} failed: {error:?}"));
    assert_eq!(result.host_calls, 0, "no host-supplied executable semantics");
    assert!(result.steps > 0);
    assert_eq!(result.returns.len(), 1);
    assert_eq!(result.returns[0].ty, ty);
    let InterpretValueKind::FloatBits(actual) = &result.returns[0].kind else {
        panic!("original {name} returned a non-float value");
    };
    assert_eq!(*actual, expected, "original {name}: IEEE bits must survive real stores and loads");
}

fn main() {
    let path = std::env::args().nth(1).expect("actual complete compiler module path");
    let bytes = std::fs::read(path).unwrap();
    let module = trust_ir::binary::deserialize_module(&bytes).expect("decode actual producer bytes");
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes,
        "complete canonical module, without projecting or rewriting any body");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "complete original module validation: {errors:?}");

    // Both signs of zero, subnormal, infinity, quiet NaN and signaling NaN,
    // plus normal boundaries and ordinary finite values. No arithmetic is used.
    let f32_bits: [u32; 16] = [
        0x0000_0000, 0x8000_0000, 0x0000_0001, 0x8000_0001,
        0x0080_0000, 0x7f7f_ffff, 0x3fc0_0000, 0xbfc0_0000,
        0x7f80_0000, 0xff80_0000, 0x7fc0_1234, 0xffc0_1234,
        0x7f80_1234, 0xff80_1234, 0x3f80_0000, 0xbf80_0000,
    ];
    let f64_bits: [u64; 16] = [
        0x0000_0000_0000_0000, 0x8000_0000_0000_0000,
        0x0000_0000_0000_0001, 0x8000_0000_0000_0001,
        0x0010_0000_0000_0000, 0x7fef_ffff_ffff_ffff,
        0x3ff8_0000_0000_0000, 0xbff8_0000_0000_0000,
        0x7ff0_0000_0000_0000, 0xfff0_0000_0000_0000,
        0x7ff8_0000_0000_1234, 0xfff8_0000_0000_1234,
        0x7ff0_0000_0000_1234, 0xfff0_0000_0000_1234,
        0x3ff0_0000_0000_0000, 0xbff0_0000_0000_0000,
    ];
    let f32_pairs: [(&str, fn(f32, f32) -> f32); 4] = [
        ("replace_f32", oracle::replace_f32),
        ("pattern_f32", oracle::pattern_f32),
        ("raw_local_f32", oracle::raw_local_f32),
        ("parameter_f32", oracle::parameter_f32),
    ];
    let f64_pairs: [(&str, fn(f64, f64) -> f64); 4] = [
        ("replace_f64", oracle::replace_f64),
        ("pattern_f64", oracle::pattern_f64),
        ("raw_local_f64", oracle::raw_local_f64),
        ("parameter_f64", oracle::parameter_f64),
    ];
    let mut cases = 0;
    for (i, replacement) in f32_bits.iter().copied().enumerate() {
        let initial = f32_bits[(i + 1) % f32_bits.len()];
        let other = f32_bits[(i + 2) % f32_bits.len()];
        for (name, oracle) in f32_pairs {
            let expected = oracle(f32::from_bits(initial), f32::from_bits(replacement)).to_bits();
            check(&module, name, vec![float32(initial), float32(replacement)], Ty::F32,
                u64::from(expected));
            cases += 1;
        }
        for choose in [true, false] {
            let expected = oracle::branch_f32(f32::from_bits(initial),
                f32::from_bits(replacement), f32::from_bits(other), choose).to_bits();
            check(&module, "branch_f32", vec![float32(initial), float32(replacement),
                float32(other), boolean(choose)], Ty::F32, u64::from(expected));
            let expected = oracle::delayed_f32(f32::from_bits(replacement),
                f32::from_bits(other), choose).to_bits();
            check(&module, "delayed_f32", vec![float32(replacement), float32(other),
                boolean(choose)], Ty::F32, u64::from(expected));
            cases += 2;
        }
    }
    for (i, replacement) in f64_bits.iter().copied().enumerate() {
        let initial = f64_bits[(i + 1) % f64_bits.len()];
        let other = f64_bits[(i + 2) % f64_bits.len()];
        for (name, oracle) in f64_pairs {
            let expected = oracle(f64::from_bits(initial), f64::from_bits(replacement)).to_bits();
            check(&module, name, vec![float64(initial), float64(replacement)], Ty::F64, expected);
            cases += 1;
        }
        for choose in [true, false] {
            let expected = oracle::branch_f64(f64::from_bits(initial),
                f64::from_bits(replacement), f64::from_bits(other), choose).to_bits();
            check(&module, "branch_f64", vec![float64(initial), float64(replacement),
                float64(other), boolean(choose)], Ty::F64, expected);
            let expected = oracle::delayed_f64(f64::from_bits(replacement),
                f64::from_bits(other), choose).to_bits();
            check(&module, "delayed_f64", vec![float64(replacement), float64(other),
                boolean(choose)], Ty::F64, expected);
            cases += 2;
        }
    }
    assert_eq!(cases, 256, "all twelve value entrypoints and both branch outcomes");
    println!("ORIGINAL_FLOAT_MODULE: {cases} actual bit-exact cases passed; empirical only");
}
