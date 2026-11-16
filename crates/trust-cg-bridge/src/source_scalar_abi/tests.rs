use super::*;

#[test]
fn mixed_scalar_arguments_use_independent_gpr_and_shared_fp_banks() {
    let params: Vec<_> =
        (0..8).flat_map(|i| [Ty::I64, if i % 2 == 0 { Ty::F32 } else { Ty::F64 }]).collect();
    assert_eq!(
        darwin_scalar("aarch64-apple-darwin", &params, &[Ty::F64]).unwrap(),
        RegisterUse { gpr: 8, fp: 8 }
    );
    assert_eq!(
        darwin_scalar("aarch64-apple-darwin", &[Ty::F32, Ty::F64], &[Ty::I32]).unwrap(),
        RegisterUse { gpr: 0, fp: 2 }
    );
}

#[test]
fn native_scalar_bank_width_and_position_mismatches_are_refused() {
    for actual in [
        vec![ArgLocation::Reg(gpr::X0)],
        vec![ArgLocation::Reg(gpr::D0)],
        vec![ArgLocation::Reg(gpr::S1)],
        vec![ArgLocation::Stack { offset: 0, size: 4 }],
    ] {
        assert!(check_locations(&[Type::F32], &actual, false).is_err(), "{actual:?}");
    }
    assert!(
        check_locations(
            &[Type::I64, Type::F64],
            &[ArgLocation::Reg(gpr::X0), ArgLocation::Reg(gpr::D1)],
            false
        )
        .is_err()
    );
    assert!(
        check_locations(
            &[Type::F32, Type::F64],
            &[ArgLocation::Reg(gpr::S0), ArgLocation::Reg(gpr::D0)],
            false
        )
        .is_err(),
        "f32/f64 share one FP bank"
    );
    assert!(check_locations(&[Type::F64], &[ArgLocation::Reg(gpr::S0)], true).is_err());
    assert!(
        check_locations(&[Type::I32], &[ArgLocation::Reg(gpr::X0)], true).is_err(),
        "narrow result uses W0"
    );
}

#[test]
fn native_scalar_target_and_aggregate_floors_stay_closed() {
    for params in [vec![Ty::F16], vec![Ty::Bool]] {
        assert!(darwin_scalar("aarch64-apple-darwin", &params, &[]).is_err());
    }
    for target in ["aarch64-unknown-linux-gnu", "x86_64-apple-darwin", "arm64-apple-macosx"] {
        assert!(darwin_scalar(target, &[Ty::F32], &[Ty::F64]).is_err());
    }
    assert!(darwin_scalar("aarch64-apple-darwin", &[Ty::F64], &[Ty::F32, Ty::F64]).is_err());
    assert!(
        check_locations(&[Type::I128], &[ArgLocation::RegPair(gpr::X0, gpr::X1)], false).is_err()
    );
}

#[test]
fn native_scalar_stack_uses_natural_packing_across_both_overflow_banks() {
    let mut params: Vec<_> = (0..8).flat_map(|_| [Ty::I64, Ty::F64]).collect();
    params.extend([Ty::I8, Ty::F32, Ty::I16, Ty::F64, Ty::I32, Ty::F32, Ty::Ptr]);
    assert_eq!(darwin_scalar("aarch64-apple-darwin", &params, &[Ty::I64]).unwrap(),
        RegisterUse { gpr: 12, fp: 11 });
    let types: Vec<_> = params.iter().map(scalar).collect::<Result<_, _>>().unwrap();
    let locations = AppleAArch64ABI::classify_params_with(AArch64AbiVariant::Darwin, &types);
    assert_eq!(&locations[16..], &[
        ArgLocation::Stack { offset: 0, size: 1 },
        ArgLocation::Stack { offset: 4, size: 4 },
        ArgLocation::Stack { offset: 8, size: 2 },
        ArgLocation::Stack { offset: 16, size: 8 },
        ArgLocation::Stack { offset: 24, size: 4 },
        ArgLocation::Stack { offset: 28, size: 4 },
        ArgLocation::Stack { offset: 32, size: 8 },
    ]);
    // Standard AAPCS64 eight-byte slots are not Darwin fixed stack arguments.
    let other = AppleAArch64ABI::classify_params_with(AArch64AbiVariant::Aapcs64, &types);
    assert!(check_locations(&types, &other, false).is_err());
    for i in 16..locations.len() {
        for replacement in [
            ArgLocation::Stack { offset: 64, size: types[i].bytes() },
            ArgLocation::Stack { offset: 0, size: 16 },
            ArgLocation::Reg(gpr::X0),
        ] {
            let mut corrupt = locations.clone();
            corrupt[i] = replacement;
            assert!(check_locations(&types, &corrupt, false).is_err(), "{i}: {corrupt:?}");
        }
    }
}

#[test]
fn native_scalar_bank_exhaustion_does_not_consume_the_other_bank() {
    let mut params = vec![Ty::U8; 10];
    params.extend([Ty::F32, Ty::F64]);
    assert_eq!(darwin_scalar("aarch64-apple-darwin", &params, &[]).unwrap(),
        RegisterUse { gpr: 10, fp: 2 });
    let mut params = vec![Ty::F32; 10];
    params.extend([Ty::Ptr, Ty::U16]);
    assert_eq!(darwin_scalar("aarch64-apple-darwin", &params, &[Ty::F32]).unwrap(),
        RegisterUse { gpr: 2, fp: 10 });
}
