use super::*;

fn round_trip(key: HoleKey) {
    let wire = encode(&key).unwrap();
    assert_eq!(decode(&wire).unwrap(), key);
    assert_eq!(encode(&decode(&wire).unwrap()).unwrap(), wire);
}

#[test]
fn nested_polymorphic_and_callable_terms_keep_every_identity_component() {
    let signature = KeyTy::FnPtr {
        inputs_and_output: vec![KeyTy::Tuple(vec![KeyTy::Param(3)]), KeyTy::Uint(64)],
        abi: "rust-call".into(), safe: true, c_variadic: false, splatted: Some(0),
    };
    let closure = KeyTy::Closure((13, 29), vec![
        KeyArg::ErasedRegion, KeyArg::Type(KeyTy::Param(3)),
        KeyArg::Type(signature), KeyArg::Type(KeyTy::Tuple(vec![KeyTy::Uint(8)])),
    ]);
    round_trip(HoleKey::Callee { item: (99, 77), args: vec![
        KeyArg::Type(closure), KeyArg::Const(KeyConst::Param(8)),
        KeyArg::Type(KeyTy::Projection { item: (5, 6), args: vec![KeyArg::Type(KeyTy::Param(3))], rigid: true }),
    ]});
    for t in [
        KeyTy::Bool, KeyTy::Char, KeyTy::Int(0), KeyTy::Int(128), KeyTy::Uint(0),
        KeyTy::Float(16), KeyTy::Float(128), KeyTy::Str, KeyTy::Never,
        KeyTy::Adt((1, 2), vec![KeyArg::Type(KeyTy::Param(0))]),
        KeyTy::Ref { mutable: true, pointee: Box::new(KeyTy::Param(0)) },
        KeyTy::RawPtr { mutable: false, pointee: Box::new(KeyTy::Uint(8)) },
        KeyTy::Slice(Box::new(KeyTy::Param(1))),
        KeyTy::Array(Box::new(KeyTy::Param(1)), KeyConst::Param(2)),
        KeyTy::Array(Box::new(KeyTy::Uint(8)), KeyConst::Value { bits: 256, bytes: 8, ty: Box::new(KeyTy::Uint(0)) }),
        KeyTy::FnDef((17, 19), vec![KeyArg::ErasedRegion]), KeyTy::Foreign((3, 4)),
    ] { round_trip(HoleKey::Type(t)); }
    round_trip(HoleKey::Const(KeyConstItem::Assoc { item: (3, 9), args: vec![KeyArg::Type(KeyTy::Param(1))] }));
    round_trip(HoleKey::Const(KeyConstItem::FieldOffset { adt: Box::new(KeyTy::Adt((1, 4), vec![KeyArg::Type(KeyTy::Param(0))])), variant: 0, field: 2 }));
}

#[test]
fn distinct_callables_never_share_a_unit_key() {
    let a = HoleKey::Type(KeyTy::Closure((1, 2), vec![]));
    let b = HoleKey::Type(KeyTy::Closure((1, 3), vec![]));
    let c = HoleKey::Type(KeyTy::FnDef((1, 2), vec![]));
    let unit = HoleKey::Type(KeyTy::Tuple(vec![]));
    let images = [a, b, c, unit].map(|k| encode(&k).unwrap().bytes);
    for (i, a) in images.iter().enumerate() { for b in &images[i + 1..] { assert_ne!(a, b); } }
}

#[test]
fn dependency_order_is_first_occurrence_without_losing_const_parameters() {
    let key = HoleKey::Callee { item: (3, 5), args: vec![
        KeyArg::Type(KeyTy::Array(Box::new(KeyTy::Param(9)), KeyConst::Param(2))),
        KeyArg::Type(KeyTy::Tuple(vec![KeyTy::Param(9), KeyTy::Param(3)])),
        KeyArg::Const(KeyConst::Param(2)), KeyArg::ErasedRegion,
    ] };
    assert_eq!(parameters(&key).unwrap(), [9, 2, 3]);
}

#[test]
fn malformed_or_noncanonical_key_bytes_are_refused() {
    let valid = encode(&HoleKey::Type(KeyTy::Ref { mutable: true, pointee: Box::new(KeyTy::Bool) })).unwrap();
    for end in 0..valid.bytes.len() {
        let mut key = valid.clone(); key.bytes.truncate(end); assert!(decode(&key).is_err());
    }
    let mut key = valid.clone(); key.namespace = "other".into(); assert!(decode(&key).is_err());
    let mut key = valid.clone(); key.bytes[8] = 99; assert!(decode(&key).is_err());
    let mut key = valid.clone(); key.bytes[12] = 99; assert!(decode(&key).is_err());
    let mut key = valid.clone(); key.bytes[14] = 2; assert!(decode(&key).is_err());
    let mut key = valid; key.bytes.push(0); assert!(decode(&key).is_err());
    for (bits, bytes, ty) in [(256, 1, KeyTy::Uint(8)), (2, 1, KeyTy::Bool),
        (0xd800, 4, KeyTy::Char), (1, 0, KeyTy::Uint(0))] {
        assert!(encode(&HoleKey::Callee { item: (1, 2), args: vec![KeyArg::Const(KeyConst::Value { bits, bytes, ty: Box::new(ty) })] }).is_err());
    }
}

#[test]
fn decoder_bounds_total_reserved_slots_and_recursive_depth() {
    let mut ty = KeyTy::Bool;
    for _ in 0..MAX_DEPTH + 1 { ty = KeyTy::Slice(Box::new(ty)); }
    assert!(encode(&HoleKey::Type(ty)).is_err());
    let mut key = encode(&HoleKey::Type(KeyTy::Tuple(vec![]))).unwrap();
    key.bytes[14..18].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(decode(&key).is_err());
}
