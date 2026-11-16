//! An ordinary-Rust consumer of the original compiler's complete binary data.
//! No private compiler metadata, body edits, host model, or proof claim.
use trust_ir::{Module, Ty};
use trust_ir::interpret::{Interpreter, InterpretValue};

fn execute(module: &Module, name: &str, args: &[u64]) -> u64 {
    // Function.name is its link-time symbol. The original source display path
    // is selector DATA only; uniqueness, exact signature and execution are
    // still checked, and it grants no source/body/proof authority.
    let functions: Vec<_> = module.functions.iter().filter(|f| {
        f.display_path.as_deref().unwrap_or(&f.name).rsplit("::").next() == Some(name)
    }).collect();
    assert_eq!(functions.len(), 1, "exact unique original function {name}");
    let f = functions[0];
    let signature = &module.func_types[f.ty.as_usize()];
    assert_eq!(signature.params, vec![Ty::U64; args.len()]);
    assert_eq!(signature.returns, vec![Ty::U64]);
    let values = args.iter().map(|a| InterpretValue::int(Ty::U64, i128::from(*a)).unwrap());
    let result = Interpreter::with_module(module).execute_func(f.id, values)
        .unwrap_or_else(|e| panic!("original {name}({args:?}) refused: {e}"));
    assert_eq!(result.host_calls, 0, "no host-supplied semantics");
    assert!(result.steps > 0);
    assert_eq!(result.returns.len(), 1);
    assert_eq!(result.returns[0].ty, Ty::U64);
    u64::try_from(result.returns[0].as_int().unwrap().as_unsigned()).unwrap()
}

fn main() {
    let path = std::env::args().nth(1).expect("actual complete module path");
    let bytes = std::fs::read(path).unwrap();
    let module = trust_ir::binary::deserialize_module(&bytes).expect("original module canonical decoding");
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes, "no projection or rewritten producer body");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "complete module validation: {errors:?}");
    let boundaries = [0, 1, 127, 128, 255, 256, (1 << 32) - 1, 1 << 32,
        (1 << 63) - 1, 1 << 63, u64::MAX - 1, u64::MAX];
    let mut cases = 0;
    for (i, x) in boundaries.into_iter().enumerate() {
        let y = boundaries[(i * 5 + 1) % boundaries.len()];
        let z = boundaries[(i * 7 + 2) % boundaries.len()];
        assert_eq!(execute(&module, "execute_one", &[x]), x);
        assert_eq!(execute(&module, "execute_two", &[x, y]), x ^ y.wrapping_shl(1));
        assert_eq!(execute(&module, "execute_rest", &[x, y, z]), x ^ z.wrapping_shl(1) ^ (1 << 32));
        assert_eq!(execute(&module, "execute_empty", &[x]), x ^ 47);
        assert_eq!(execute(&module, "execute_byte_pair", &[x, y]), (x & 255) ^ ((y & 255) << 8));
        assert_eq!(execute(&module, "execute_zst", &[x]), x ^ (1 << 32));
        assert_eq!(execute(&module, "execute_reference_join", &[x, y]), y);
        assert_eq!(execute(&module, "execute_overlap", &[x, y]), y);
        assert_eq!(execute(&module, "execute_zst_repeat", &[x]), x ^ (1 << 32));
        let ordered = x.wrapping_mul(3).wrapping_add(1)
            .wrapping_mul(5).wrapping_add(2).wrapping_mul(7).wrapping_add(3);
        assert_eq!(execute(&module, "execute_unit_array_effects", &[x]), ordered ^ (1 << 32));
        assert_eq!(execute(&module, "execute_unit_array_diverge", &[x]), x ^ 7);
        cases += 11;
    }
    println!("ORIGINAL_COMPLETE_MODULE_INTERPRETER: {cases} actual boundary cases passed; host_calls=0; empirical only");
}
