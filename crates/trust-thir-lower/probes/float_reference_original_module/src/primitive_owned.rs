//! Execute the unchanged complete producer module against independently compiled
//! Rust source bodies. This is finite empirical evidence, never proof authority.
use std::collections::BTreeSet;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{Inst, Module, Ty};

#[path = "../../../../../tests/run-make/trust-primitive-owned-storage/subject.rs"]
mod oracle;

trait Primitive: Copy {
    fn ir(self) -> InterpretValue;
}
macro_rules! integer {
    ($rust:ty, $ir:ident) => {
        impl Primitive for $rust {
            fn ir(self) -> InterpretValue {
                InterpretValue::int_at(Ty::$ir, self as i128, usize::BITS).unwrap()
            }
        }
    };
}
integer!(i8, I8); integer!(i16, I16); integer!(i32, I32);
integer!(i64, I64); integer!(i128, I128); integer!(isize, Isize);
integer!(u8, U8); integer!(u16, U16); integer!(u32, U32);
integer!(u64, U64); integer!(u128, U128); integer!(usize, Usize);
impl Primitive for bool {
    fn ir(self) -> InterpretValue { InterpretValue::bool(self) }
}
impl Primitive for char {
    fn ir(self) -> InterpretValue {
        InterpretValue::int_at(Ty::Char, self as u32 as i128, usize::BITS).unwrap()
    }
}
impl Primitive for f32 {
    fn ir(self) -> InterpretValue {
        InterpretValue { ty: Ty::F32, kind: InterpretValueKind::FloatBits(u64::from(self.to_bits())) }
    }
}
impl Primitive for f64 {
    fn ir(self) -> InterpretValue {
        InterpretValue { ty: Ty::F64, kind: InterpretValueKind::FloatBits(self.to_bits()) }
    }
}
impl Primitive for () {
    fn ir(self) -> InterpretValue { InterpretValue { ty: Ty::Unit, kind: InterpretValueKind::Unit } }
}
fn tuple<const N: usize>(values: [InterpretValue; N]) -> InterpretValue {
    InterpretValue {
        ty: Ty::Tuple(values.iter().map(|value| value.ty.clone()).collect()),
        kind: InterpretValueKind::Aggregate(Vec::from(values)),
    }
}
fn short_name(function: &trust_ir::Function) -> &str {
    function.display_path.as_deref().unwrap_or(&function.name).rsplit("::").next().unwrap()
}
fn function<'a>(module: &'a Module, name: &str) -> &'a trust_ir::Function {
    let found: Vec<_> = module.functions.iter().filter(|f| short_name(f) == name).collect();
    assert_eq!(found.len(), 1, "one exact original function {name}");
    assert!(!found[0].blocks.is_empty(), "original definition, not a declaration");
    found[0]
}
fn check(module: &Module, name: &str, args: Vec<InterpretValue>, expected: InterpretValue) {
    let function = function(module, name);
    let signature = &module.func_types[function.ty.as_usize()];
    assert_eq!(signature.params, args.iter().map(|v| v.ty.clone()).collect::<Vec<_>>());
    assert_eq!(signature.returns, vec![expected.ty.clone()]);
    let result = Interpreter::with_module(module).execute_func(function.id, args)
        .unwrap_or_else(|error| panic!("original {name} failed: {error:?}"));
    assert_eq!(result.host_calls, 0, "no host-supplied executable semantics");
    assert!(result.steps > 0);
    assert_eq!(result.returns, vec![expected], "original {name}: exact native Rust result, including IEEE bits");
}
fn home_shape(module: &Module, suffix: &str, ty: Ty) {
    let delayed = function(module, &format!("delayed_{suffix}"));
    let homes: Vec<_> = delayed.blocks.iter().flat_map(|b| &b.body).filter_map(|node| {
        match &node.inst {
            Inst::Alloca { ty: allocated, .. } if allocated == &ty => {
                assert_eq!(node.results.len(), 1);
                Some(node.results[0])
            }
            _ => None,
        }
    }).collect();
    assert_eq!(homes.len(), 1, "one delayed owned primitive home: {suffix}");
    let entry = delayed.blocks.iter().find(|b| b.id == delayed.entry).unwrap();
    assert!(!entry.body.iter().any(|node| matches!(&node.inst,
        Inst::Store { ptr, .. } if ptr == &homes[0])),
        "no entry initializer fabricated before the source branch: {suffix}");
    let stores = delayed.blocks.iter().flat_map(|b| &b.body).filter(|node| matches!(&node.inst,
        Inst::Store { ptr, ty: stored, .. } if ptr == &homes[0] && stored == &ty)).count();
    assert_eq!(stores, if matches!(suffix, "char" | "unit") { 3 } else { 2 },
        "both actual branch assignments, plus Char/Unit's explicit later local assignment");
    let nested = function(module, &format!("nested_{suffix}"));
    let homes: Vec<_> = nested.blocks.iter().flat_map(|b| &b.body).filter_map(|node| {
        match &node.inst {
            Inst::Alloca { ty: allocated, .. } if allocated == &ty => {
                assert_eq!(node.results.len(), 1);
                Some(node.results[0])
            }
            _ => None,
        }
    }).collect();
    assert_eq!(homes.len(), 2, "two independent by-value leaf homes: {suffix}");
    assert_ne!(homes[0], homes[1], "destructured siblings cannot share their owned slot");
}
fn family<T: Primitive>(module: &Module, suffix: &str, values: &[T],
    delayed: fn(T, T, T, bool) -> (T, T),
    flat: fn(T, T, T) -> (T, T, T),
    nested: fn(T, T, T, T) -> (T, T, T, T, T),
    parameter: fn((T, T), T) -> (T, T, T)) -> usize
{
    home_shape(module, suffix, values[0].ir().ty);
    let mut cases = 0;
    for (i, a) in values.iter().copied().enumerate() {
        let b = values[(i + 1) % values.len()];
        let c = values[(i + 2) % values.len()];
        let replacement = values[(i + 3) % values.len()];
        for flag in [false, true] {
            let expected = delayed(a, b, replacement, flag);
            check(module, &format!("delayed_{suffix}"),
                vec![a.ir(), b.ir(), replacement.ir(), flag.ir()],
                tuple([expected.0.ir(), expected.1.ir()]));
            cases += 1;
        }
        let expected = flat(a, b, replacement);
        check(module, &format!("tuple_{suffix}"), vec![a.ir(), b.ir(), replacement.ir()],
            tuple([expected.0.ir(), expected.1.ir(), expected.2.ir()]));
        let expected = nested(a, b, c, replacement);
        check(module, &format!("nested_{suffix}"), vec![a.ir(), b.ir(), c.ir(), replacement.ir()],
            tuple([expected.0.ir(), expected.1.ir(), expected.2.ir(), expected.3.ir(), expected.4.ir()]));
        let expected = parameter((a, b), replacement);
        check(module, &format!("parameter_{suffix}"), vec![tuple([a.ir(), b.ir()]), replacement.ir()],
            tuple([expected.0.ir(), expected.1.ir(), expected.2.ir()]));
        cases += 3;
    }
    cases
}
fn main() {
    let bytes = std::fs::read(std::env::args().nth(1).expect("actual complete compiler module path")).unwrap();
    let module = trust_ir::binary::deserialize_module(&bytes).expect("decode actual producer bytes");
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes,
        "complete canonical original module, without projection, body replacement or rewriting");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "complete original module validation: {errors:?}");
    assert_eq!(module.target_info.as_ref().expect("actual compiler target").pointer_size * 8,
        usize::BITS, "native Rust oracle and IR must use the same pointer width");
    let families = ["bool", "char", "i8", "i16", "i32", "i64", "i128", "isize",
        "u8", "u16", "u32", "u64", "u128", "usize", "f32", "f64", "unit"];
    let mut expected_names = BTreeSet::new();
    for suffix in families {
        for prefix in ["store", "delayed", "tuple", "nested", "parameter"] {
            expected_names.insert(if prefix == "store" && matches!(suffix, "char" | "unit") {
                format!("identity_{suffix}")
            } else { format!("{prefix}_{suffix}") });
        }
    }
    expected_names.insert("struct_i32".into());
    expected_names.insert("array_i32".into());
    assert_eq!(module.functions.len(), 87, "complete original source population");
    let actual_names: BTreeSet<_> = module.functions.iter().map(|f| short_name(f).to_owned()).collect();
    assert_eq!(actual_names, expected_names, "exact identities, no missing or substituted helper");
    let mut cases = 0;
    cases += family(&module, "i8", &[i8::MIN, -1, 0, 1, i8::MAX], oracle::delayed_i8, oracle::tuple_i8, oracle::nested_i8, oracle::parameter_i8);
    cases += family(&module, "i16", &[i16::MIN, -1, 0, 1, i16::MAX], oracle::delayed_i16, oracle::tuple_i16, oracle::nested_i16, oracle::parameter_i16);
    cases += family(&module, "i32", &[i32::MIN, -1, 0, 1, i32::MAX], oracle::delayed_i32, oracle::tuple_i32, oracle::nested_i32, oracle::parameter_i32);
    cases += family(&module, "i64", &[i64::MIN, -1, 0, 1, i64::MAX], oracle::delayed_i64, oracle::tuple_i64, oracle::nested_i64, oracle::parameter_i64);
    cases += family(&module, "i128", &[i128::MIN, -1, 0, 1, i128::MAX], oracle::delayed_i128, oracle::tuple_i128, oracle::nested_i128, oracle::parameter_i128);
    cases += family(&module, "isize", &[isize::MIN, -1, 0, 1, isize::MAX], oracle::delayed_isize, oracle::tuple_isize, oracle::nested_isize, oracle::parameter_isize);
    cases += family(&module, "u8", &[0u8, 1, u8::MAX / 2, u8::MAX - 1, u8::MAX], oracle::delayed_u8, oracle::tuple_u8, oracle::nested_u8, oracle::parameter_u8);
    cases += family(&module, "u16", &[0u16, 1, u16::MAX / 2, u16::MAX - 1, u16::MAX], oracle::delayed_u16, oracle::tuple_u16, oracle::nested_u16, oracle::parameter_u16);
    cases += family(&module, "u32", &[0u32, 1, u32::MAX / 2, u32::MAX - 1, u32::MAX], oracle::delayed_u32, oracle::tuple_u32, oracle::nested_u32, oracle::parameter_u32);
    cases += family(&module, "u64", &[0u64, 1, u64::MAX / 2, u64::MAX - 1, u64::MAX], oracle::delayed_u64, oracle::tuple_u64, oracle::nested_u64, oracle::parameter_u64);
    cases += family(&module, "u128", &[0u128, 1, u128::MAX / 2, u128::MAX - 1, u128::MAX], oracle::delayed_u128, oracle::tuple_u128, oracle::nested_u128, oracle::parameter_u128);
    cases += family(&module, "usize", &[0usize, 1, usize::MAX / 2, usize::MAX - 1, usize::MAX], oracle::delayed_usize, oracle::tuple_usize, oracle::nested_usize, oracle::parameter_usize);
    cases += family(&module, "bool", &[false, true], oracle::delayed_bool, oracle::tuple_bool, oracle::nested_bool, oracle::parameter_bool);
    cases += family(&module, "char", &['\0', 'A', '\u{1f980}', '\u{10ffff}'], oracle::delayed_char, oracle::tuple_char, oracle::nested_char, oracle::parameter_char);
    cases += family(&module, "unit", &[()], oracle::delayed_unit, oracle::tuple_unit, oracle::nested_unit, oracle::parameter_unit);
    // Both signed zeros, subnormals, infinities, quiet/signaling NaN payloads,
    // finite boundaries and ordinary values. Exact bits, never float equality.
    let f32_values = [0x00000000u32, 0x80000000, 0x00000001, 0x80000001,
        0x00800000, 0x7f7fffff, 0x3fc00000, 0xbfc00000,
        0x7f800000, 0xff800000, 0x7fc01234, 0xffc01234,
        0x7f801234, 0xff801234, 0x3f800000, 0xbf800000].map(f32::from_bits);
    let f64_values = [0x0000000000000000u64, 0x8000000000000000,
        0x0000000000000001, 0x8000000000000001, 0x0010000000000000, 0x7fefffffffffffff,
        0x3ff8000000000000, 0xbff8000000000000, 0x7ff0000000000000, 0xfff0000000000000,
        0x7ff8000000001234, 0xfff8000000001234, 0x7ff0000000001234, 0xfff0000000001234,
        0x3ff0000000000000, 0xbff0000000000000].map(f64::from_bits);
    cases += family(&module, "f32", &f32_values, oracle::delayed_f32, oracle::tuple_f32, oracle::nested_f32, oracle::parameter_f32);
    cases += family(&module, "f64", &f64_values, oracle::delayed_f64, oracle::tuple_f64, oracle::nested_f64, oracle::parameter_f64);
    let values = [i32::MIN, -1, 0, 1, i32::MAX];
    for (i, a) in values.iter().copied().enumerate() {
        let b = values[(i + 1) % values.len()];
        let replacement = values[(i + 2) % values.len()];
        for (name, oracle) in [("struct_i32", oracle::struct_i32 as fn(i32, i32, i32) -> (i32, i32, i32)),
            ("array_i32", oracle::array_i32)]
        {
            let expected = oracle(a, b, replacement);
            check(&module, name, vec![a.ir(), b.ir(), replacement.ir()],
                tuple([expected.0.ir(), expected.1.ir(), expected.2.ir()]));
            cases += 1;
        }
    }
    assert_eq!(cases, 505, "all 17 primitive families, both branch outcomes, independent leaves and both extra patterns");
    println!("ORIGINAL_PRIMITIVE_OWNED_MODULE: {cases} exact native-Rust oracle cases; empirical only");
}
