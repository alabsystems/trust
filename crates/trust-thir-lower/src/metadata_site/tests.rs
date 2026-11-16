//! Pure inverse controls use the actual unchanged lineage encoder. Fake DefIds
//! here exercise only the codec; Rust-owner recovery has separate native TCX
//! controls and must never accept this test resolver as metadata authority.

use rustc_span::def_id::{CrateNum, DefIndex};

use super::*;
use crate::lineage::{
    ConcreteCalleeKey as Key, ConcreteExistentialPredicate as Predicate,
    ConcreteInstanceArg as Arg, ConcreteInstanceConst as Const, ConcreteInstanceKind as Kind,
    ConcreteInstanceTy as Ty, ConcreteInstanceValTree as Tree, ConcreteTerm as Term,
    DefinitionIdentity,
};

fn identity() -> DefinitionIdentity {
    DefinitionIdentity::test_only(1, 2)
}
fn resolve((krate, index): StableDef) -> Result<DefId> {
    Ok(DefId {
        krate: CrateNum::from_u32(u32::try_from(krate).map_err(|_| SiteError("test crate"))?),
        index: DefIndex::from_u32(u32::try_from(index).map_err(|_| SiteError("test index"))?),
    })
}
fn key(args: Vec<Arg>) -> String {
    Key::test_only(identity(), Kind::Item, args).symbol_suffix()
}
fn value(ty: Ty, bits: u128, bytes: u64) -> Const {
    Const::Value(ty, Tree::Leaf(bits, bytes))
}
fn decoded(args: Vec<Arg>) -> Decoded {
    decode(&key(args), &mut resolve).unwrap()
}

#[test]
fn complete_legacy_type_and_positional_vocabulary() {
    let def = identity();
    let args = vec![
        Arg::ErasedRegion,
        Arg::Ty(Ty::Bool),
        Arg::Const(value(Ty::Uint(ty::UintTy::U8), 7, 1)),
    ];
    let kinds = [
        SiteClosureKind::Closure,
        SiteClosureKind::CoroutineClosure,
        SiteClosureKind::Coroutine,
        SiteClosureKind::CoroutineWitness,
    ];
    let mut types = vec![
        Ty::Bool,
        Ty::Char,
        Ty::Str,
        Ty::Never,
        Ty::Foreign(def),
        Ty::Tuple(vec![]),
        Ty::Tuple(vec![Ty::Bool, Ty::Char]),
        Ty::Adt(def, args.clone()),
        Ty::FnDef(def, args.clone()),
        Ty::Array(Box::new(Ty::Bool), u64::MAX),
        Ty::Slice(Box::new(Ty::Char)),
        Ty::Ref(Box::new(Ty::Bool), ty::Mutability::Not),
        Ty::Ref(Box::new(Ty::Bool), ty::Mutability::Mut),
        Ty::RawPtr(Box::new(Ty::Bool), ty::Mutability::Not),
        Ty::RawPtr(Box::new(Ty::Bool), ty::Mutability::Mut),
    ];
    for kind in [
        ty::IntTy::Isize,
        ty::IntTy::I8,
        ty::IntTy::I16,
        ty::IntTy::I32,
        ty::IntTy::I64,
        ty::IntTy::I128,
    ] {
        types.push(Ty::Int(kind));
    }
    for kind in [
        ty::UintTy::Usize,
        ty::UintTy::U8,
        ty::UintTy::U16,
        ty::UintTy::U32,
        ty::UintTy::U64,
        ty::UintTy::U128,
    ] {
        types.push(Ty::Uint(kind));
    }
    for kind in [ty::FloatTy::F16, ty::FloatTy::F32, ty::FloatTy::F64, ty::FloatTy::F128] {
        types.push(Ty::Float(kind));
    }
    for kind in kinds {
        types.push(Ty::ClosureLike(kind, def, args.clone()));
    }
    types.push(Ty::Dynamic(vec![
        Predicate::Trait(def, args.clone()),
        Predicate::Projection(def, args.clone(), Box::new(Term::Ty(Ty::Bool))),
        Predicate::Projection(def, args.clone(), Box::new(Term::Const(value(Ty::Bool, 1, 1)))),
        Predicate::AutoTrait(def),
    ]));
    for abi in ["Rust", "C", "rust-call"] {
        for safe in [false, true] {
            for c_variadic in [false, true] {
                // Headers are accepted only where Rustc's own constructor permits them.
                if ty::FnSigKind::new(
                    abi.parse().unwrap(),
                    if safe { rustc_hir::Safety::Safe } else { rustc_hir::Safety::Unsafe },
                    c_variadic,
                    None,
                    1,
                )
                .is_ok()
                {
                    types.push(Ty::FnPtr {
                        inputs_and_output: vec![Ty::Bool, Ty::Char],
                        abi: abi.into(),
                        safe,
                        c_variadic,
                        splatted: None,
                    });
                }
            }
        }
    }
    for index in [0, 1] {
        if ty::FnSigKind::new(
            rustc_abi::ExternAbi::Rust,
            rustc_hir::Safety::Safe,
            false,
            Some(index),
            2,
        )
        .is_ok()
        {
            types.push(Ty::FnPtr {
                inputs_and_output: vec![Ty::Bool, Ty::Tuple(vec![]), Ty::Char],
                abi: "Rust".into(),
                safe: true,
                c_variadic: false,
                splatted: Some(index),
            });
        }
    }
    let count = types.len();
    let all = types.into_iter().map(Arg::Ty).chain(args.clone()).collect();
    let decoded = decoded(all);
    assert_eq!(decoded.args.len(), count + args.len());
    assert_eq!(
        &decoded.args[count..],
        &[
            SiteArg::ErasedRegion,
            SiteArg::Ty(SiteTy::Bool),
            SiteArg::Const(SiteConst::Value(SiteTy::Uint(ty::UintTy::U8), SiteValTree::Leaf(7, 1)))
        ]
    );
    assert!(
        matches!(&decoded.args[7], SiteArg::Ty(SiteTy::Adt(_, args)) if args.len()==3 && args[0]==SiteArg::ErasedRegion)
    );
    assert!(
        matches!(&decoded.args[8], SiteArg::Ty(SiteTy::FnDef(_, args)) if matches!(args[2], SiteArg::Const(_)))
    );
    for (index, kind) in kinds.into_iter().enumerate() {
        assert!(
            matches!(&decoded.args[31+index], SiteArg::Ty(SiteTy::ClosureLike(actual, _, _)) if *actual==kind)
        );
    }
}

#[test]
fn complete_nested_typed_valtrees_and_same_signature_sites_remain_distinct() {
    let nested = Const::Value(
        Ty::Tuple(vec![Ty::Bool, Ty::Array(Box::new(Ty::Uint(ty::UintTy::U16)), 2)]),
        Tree::Branch(vec![
            value(Ty::Bool, 1, 1),
            Const::Value(
                Ty::Array(Box::new(Ty::Uint(ty::UintTy::U16)), 2),
                Tree::Branch(vec![
                    value(Ty::Uint(ty::UintTy::U16), 5, 2),
                    value(Ty::Uint(ty::UintTy::U16), 65535, 2),
                ]),
            ),
        ]),
    );
    let one = key(vec![Arg::Const(nested)]);
    let parsed = decode(&one, &mut resolve).unwrap();
    assert!(
        matches!(&parsed.args[0], SiteArg::Const(SiteConst::Value(SiteTy::Tuple(_), SiteValTree::Branch(values))) if values.len()==2)
    );
    let a = key(vec![Arg::Const(value(Ty::Uint(ty::UintTy::U64), 1, 8))]);
    let b = key(vec![Arg::Const(value(Ty::Uint(ty::UintTy::U64), 2, 8))]);
    let c = key(vec![Arg::Ty(Ty::Uint(ty::UintTy::U64))]);
    let d = key(vec![Arg::Ty(Ty::Int(ty::IntTy::I64))]);
    assert_ne!(a, b);
    assert_ne!(decode(&a, &mut resolve).unwrap().args, decode(&b, &mut resolve).unwrap().args);
    assert_ne!(c, d);
    assert_ne!(decode(&c, &mut resolve).unwrap().args, decode(&d, &mut resolve).unwrap().args);
}

fn bytes(hex: &str) -> Vec<u8> {
    hex.as_bytes()
        .chunks_exact(2)
        .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
        .collect()
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn refuses(bytes: &[u8]) {
    assert!(decode(&hex(bytes), &mut resolve).is_err());
}

#[test]
fn all_prefixes_bad_discriminators_noncanonical_hex_and_unknown_data_refuse() {
    let good = key(vec![Arg::Ty(Ty::Bool)]);
    for end in 0..good.len() {
        assert!(decode(&good[..end], &mut resolve).is_err(), "prefix {end}");
    }
    let raw = bytes(&good);
    for (at, tags) in
        [(0, vec![0, 2, 255]), (17, vec![2, 255]), (26, vec![3, 255]), (27, vec![12, 13, 20, 255])]
    {
        for tag in tags {
            let mut bad = raw.clone();
            bad[at] = tag;
            refuses(&bad);
        }
    }
    assert!(decode(&(good.clone() + "00"), &mut resolve).is_err());
    assert!(decode(&good.replace('0', "G"), &mut resolve).is_err());
    let mut upper = key(vec![Arg::Const(value(Ty::Uint(ty::UintTy::U8), 255, 1))]);
    upper.make_ascii_uppercase();
    assert!(decode(&upper, &mut resolve).is_err());
    let mut bad = raw.clone();
    bad[18..26].copy_from_slice(&u64::MAX.to_be_bytes());
    refuses(&bad);
    let reify = Key::test_only(identity(), Kind::ReifyShim, vec![]).symbol_suffix();
    assert_eq!(decode(&reify, &mut resolve).unwrap().kind, InstanceKind::ReifyShim);
}

#[test]
fn every_leaf_and_nested_discriminator_refuses_invalid_values() {
    for (ty, offset) in [
        (Ty::Ref(Box::new(Ty::Bool), ty::Mutability::Not), 28),
        (Ty::RawPtr(Box::new(Ty::Bool), ty::Mutability::Not), 28),
        (Ty::ClosureLike(SiteClosureKind::Closure, identity(), vec![]), 28),
    ] {
        let mut bad = bytes(&key(vec![Arg::Ty(ty)]));
        bad[offset] = 255;
        refuses(&bad);
    }
    for ty in [Ty::Int(ty::IntTy::I8), Ty::Uint(ty::UintTy::U8), Ty::Float(ty::FloatTy::F16)] {
        let mut bad = bytes(&key(vec![Arg::Ty(ty)]));
        *bad.last_mut().unwrap() = b'x';
        refuses(&bad);
    }
    let mut bad = bytes(&key(vec![Arg::Const(value(Ty::Bool, 1, 1))]));
    bad[28] = 255;
    refuses(&bad);
    for (bits, width) in [(1, 0), (1, 17), (256, 1), (u128::MAX, 8)] {
        assert!(
            decode(
                &key(vec![Arg::Const(value(Ty::Uint(ty::UintTy::U8), bits, width))]),
                &mut resolve
            )
            .is_err()
        );
    }
    for predicates in [
        vec![Predicate::Trait(identity(), vec![])],
        vec![Predicate::Projection(identity(), vec![], Box::new(Term::Ty(Ty::Bool)))],
    ] {
        let mut bad = bytes(&key(vec![Arg::Ty(Ty::Dynamic(predicates))]));
        bad[36] = 255;
        refuses(&bad);
    }
    let mut bad = bytes(&key(vec![Arg::Ty(Ty::Dynamic(vec![Predicate::Projection(
        identity(),
        vec![],
        Box::new(Term::Ty(Ty::Bool)),
    )]))]));
    bad[61] = 255;
    refuses(&bad);
}

#[test]
fn bounded_tree_and_allocation_controls_refuse_before_unbounded_work() {
    let mut raw = bytes(&key(vec![Arg::Ty(Ty::Bool)]));
    raw[18..26].copy_from_slice(&((MAX_NODES + 1) as u64).to_be_bytes());
    refuses(&raw);
    let mut ty = Ty::Bool;
    for _ in 0..=MAX_DEPTH {
        ty = Ty::Slice(Box::new(ty));
    }
    assert!(decode(&key(vec![Arg::Ty(ty)]), &mut resolve).is_err());
    assert!(decode(&"00".repeat(MAX_BYTES + 1), &mut resolve).is_err());
    // The grammar contains no reference/back-edge tag. Recursive hostile
    // bytes can only spell a finite tree; depth/size budgets bound that tree.
    let mut cyclic = bytes(&key(vec![Arg::Ty(Ty::Bool)]));
    cyclic[27] = 255;
    refuses(&cyclic);
    let mut calls = 0;
    assert!(
        decode(&key(vec![]), &mut |_| {
            calls += 1;
            Err(SiteError("unloaded"))
        })
        .is_err()
    );
    assert_eq!(calls, 1);
}
