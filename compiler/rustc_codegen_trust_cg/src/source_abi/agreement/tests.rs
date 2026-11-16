use trust_ir::{ClosureLayoutDescriptor, ClosureTy, FuncTy};

use super::*;

fn pointer() -> Scalar {
    Scalar::Pointer
}
fn byte() -> Scalar {
    Scalar::Int { bits: 8, signed: false }
}
fn lane(scalar: Scalar) -> Lane {
    Lane { scalar, extension: Extension::None, inreg: false }
}
fn fixture(captures: Vec<Ty>, frame: &ObservedFrame) -> Module {
    let mut m = Module::new("source_abi");
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let func = m
        .add_func_type(FuncTy { params: vec![], returns: vec![], abi: None, is_vararg: false })
        .unwrap();
    m.closure_types.push(ClosureTy { func, captures });
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: frame.size,
        align: frame.align,
        capture_offsets: frame.offsets.clone(),
    });
    m
}
fn pair() -> (ObservedFrame, Transport) {
    (
        ObservedFrame {
            size: 16,
            align: 8,
            offsets: vec![0, 8],
            captures: vec![pointer(), byte()],
        },
        Transport::Pair([lane(pointer()), lane(byte())]),
    )
}
#[test]
fn observed_scalar_and_pair_environments_keep_their_exact_images() {
    let (frame, mode) = pair();
    let module = fixture(vec![Ty::Ptr, Ty::U8], &frame);
    let before = module.clone();
    assert_eq!(closure_transport(&module, ClosureTyId::new(0), &frame, &mode).unwrap(), 2);
    assert_eq!(module, before);
    let frame = ObservedFrame { size: 8, align: 8, offsets: vec![0], captures: vec![pointer()] };
    let module = fixture(vec![Ty::Ptr], &frame);
    assert_eq!(
        closure_transport(
            &module,
            ClosureTyId::new(0),
            &frame,
            &Transport::Direct(lane(pointer()))
        )
        .unwrap(),
        1
    );
}
#[test]
fn reordered_captures_follow_the_observed_physical_pair() {
    let (mut frame, mode) = pair();
    frame.captures.reverse();
    frame.offsets.reverse();
    let module = fixture(vec![Ty::U8, Ty::Ptr], &frame);
    assert_eq!(closure_transport(&module, ClosureTyId::new(0), &frame, &mode).unwrap(), 2);
    let wrong = Transport::Pair([lane(byte()), lane(pointer())]);
    assert!(closure_transport(&module, ClosureTyId::new(0), &frame, &wrong).is_err());
}
#[test]
fn native_one_word_aggregate_cannot_impersonate_a_rust_scalar_pair() {
    let word = Scalar::Int { bits: 32, signed: false };
    let frame =
        ObservedFrame { size: 8, align: 4, offsets: vec![0, 4], captures: vec![word, word] };
    let module = fixture(vec![Ty::U32, Ty::U32], &frame);
    assert!(
        closure_transport(
            &module,
            ClosureTyId::new(0),
            &frame,
            &Transport::Pair([lane(word), lane(word)])
        )
        .is_err()
    );
}
#[test]
fn absent_drifted_or_attribute_bearing_frames_refuse() {
    let (frame, mode) = pair();
    for change in 0..5 {
        let mut module = fixture(vec![Ty::Ptr, Ty::U8], &frame);
        match change {
            0 => module.closure_layouts.clear(),
            1 => module.closure_layouts[0].size = 24,
            2 => module.closure_layouts[0].capture_offsets = vec![8, 0],
            3 => module.closure_types[0].captures[1] = Ty::U64,
            _ => module.closure_layouts.push(module.closure_layouts[0].clone()),
        }
        assert!(closure_transport(&module, ClosureTyId::new(0), &frame, &mode).is_err());
    }
    for ext in [Extension::Zext, Extension::Sext] {
        let bad = Transport::Pair([Lane { extension: ext, ..lane(pointer()) }, lane(byte())]);
        assert!(
            closure_transport(
                &fixture(vec![Ty::Ptr, Ty::U8], &frame),
                ClosureTyId::new(0),
                &frame,
                &bad
            )
            .is_err()
        );
    }
}
#[test]
fn c_unsigned_byte_extension_is_exact_and_not_a_dropped_contract() {
    let extended = Lane { extension: Extension::Zext, ..lane(byte()) };
    assert!(scalar_transport(&Ty::U8, extended, true).is_ok());
    // The unchanged logical scalar is still8 bits: agreement does not
    // rewrite it to a32-bit type or discard the observed Zext marker.
    assert_eq!(extended, Lane { scalar: byte(), extension: Extension::Zext, inreg: false });
    assert!(scalar_transport(&Ty::U8, Lane { inreg: true, ..extended }, true).is_err());
    for (ty, bits) in [(Ty::U32, 32), (Ty::U64, 64)] {
        let wider = Lane { scalar: Scalar::Int { bits, signed: false }, ..extended };
        assert!(scalar_transport(&ty, wider, true).is_err());
    }

    assert!(scalar_transport(&Ty::U8, extended, false).is_err());
    assert!(scalar_transport(&Ty::I8, extended, true).is_err());
    assert!(
        scalar_transport(&Ty::U8, Lane { extension: Extension::Sext, ..extended }, true).is_err()
    );
    assert!(scalar_transport(&Ty::Ptr, Lane { inreg: true, ..lane(pointer()) }, true).is_err());
}
#[test]
fn thin_pointer_transport_keeps_actual_type_extension_and_placement() {
    let plain = lane(pointer());
    for apple_c in [false, true] {
        assert_eq!(scalar_transport(&Ty::Ptr, plain, apple_c).unwrap(), RegisterUse::integer(1));
        assert!(scalar_transport(&Ty::U64, plain, apple_c).is_err());
        for bad in [
            Lane { extension: Extension::Zext, ..plain },
            Lane { extension: Extension::Sext, ..plain },
            Lane { inreg: true, ..plain },
            Lane { scalar: Scalar::Int { bits: 64, signed: false }, ..plain },
        ] {
            assert!(scalar_transport(&Ty::Ptr, bad, apple_c).is_err());
        }
    }
}
#[test]
fn c_unsigned_halfword_extension_preserves_actual_type_flags_and_refusals() {
    let plain = Lane {
        scalar: Scalar::Int { bits: 16, signed: false },
        extension: Extension::None,
        inreg: false,
    };
    let extended = Lane { extension: Extension::Zext, ..plain };
    assert!(scalar_transport(&Ty::U16, extended, true).is_ok());
    assert!(scalar_transport(&Ty::U16, plain, false).is_ok());
    assert_eq!(extended.scalar, Scalar::Int { bits: 16, signed: false });
    assert_eq!(extended.extension, Extension::Zext);
    for (ty, lane, apple_c) in [
        (Ty::U16, extended, false),
        (Ty::I16, extended, true),
        (Ty::U8, extended, true),
        (Ty::U16, Lane { inreg: true, ..extended }, true),
        (Ty::U16, Lane { extension: Extension::Sext, ..plain }, true),
        (Ty::U32, Lane { scalar: Scalar::Int { bits: 32, signed: false }, ..extended }, true),
    ] {
        assert!(scalar_transport(&ty, lane, apple_c).is_err());
    }
}
#[test]
fn signed_small_scalars_preserve_actual_sext_and_reject_weaker_flags() {
    for (ty, bits) in [(Ty::I8, 8), (Ty::I16, 16)] {
        let actual = Lane {
            scalar: Scalar::Int { bits, signed: true },
            extension: Extension::Sext,
            inreg: false,
        };
        assert!(scalar_transport(&ty, actual, true).is_ok());
        assert_eq!(actual.extension, Extension::Sext);
        assert!(
            scalar_transport(&ty, Lane { extension: Extension::None, ..actual }, true).is_err()
        );
        assert!(scalar_transport(&ty, actual, false).is_err());
        assert!(scalar_transport(&ty, Lane { inreg: true, ..actual }, true).is_err());
        assert!(
            scalar_transport(&ty, Lane { extension: Extension::Zext, ..actual }, true).is_err()
        );
        assert!(
            scalar_transport(
                &ty,
                Lane { scalar: Scalar::Int { bits, signed: false }, ..actual },
                true
            )
            .is_err()
        );
        assert!(
            scalar_transport(&ty, Lane { extension: Extension::None, ..actual }, false).is_ok()
        );
    }
}

#[test]
fn source_fp_width_extension_and_register_bank_are_exact() {
    for (ty, bits, wrong) in [(Ty::F32, 32, Ty::F64), (Ty::F64, 64, Ty::F32)] {
        let actual = lane(Scalar::Float { bits });
        for apple_c in [false, true] {
            assert_eq!(scalar_transport(&ty, actual, apple_c).unwrap(), RegisterUse { gpr: 0, fp: 1 });
            for other in [&wrong, &Ty::I32, &Ty::U64, &Ty::Ptr] {
                assert!(scalar_transport(other, actual, apple_c).is_err());
            }
            for damaged in [Lane { extension: Extension::Zext, ..actual }, Lane { extension: Extension::Sext, ..actual }, Lane { inreg: true, ..actual }] {
                assert!(scalar_transport(&ty, damaged, apple_c).is_err());
            }
        }
    }
    for bits in [16, 128] {
        assert!(scalar_transport(&Ty::F32, lane(Scalar::Float { bits }), false).is_err());
    }
}

#[test]
fn source_scalar_occupancy_never_counts_fp_into_integer_registers() {
    let mut used = RegisterUse::default();
    for _ in 0..8 {
        used.add(scalar_transport(&Ty::F64, lane(Scalar::Float { bits: 64 }), false).unwrap());
        used.add(scalar_transport(&Ty::Ptr, lane(pointer()), false).unwrap());
    }
    assert_eq!(used, RegisterUse { gpr: 8, fp: 8 });
}

#[test]
fn fp_closure_captures_do_not_inherit_scalar_transport_permission() {
    for (ty, bits) in [(Ty::F32, 32), (Ty::F64, 64)] {
        let frame = ObservedFrame { size: u64::from(bits / 8), align: u64::from(bits / 8), offsets: vec![0], captures: vec![Scalar::Float { bits }] };
        let module = fixture(vec![ty], &frame);
        assert!(closure_transport(&module, ClosureTyId::new(0), &frame, &Transport::Direct(lane(Scalar::Float { bits }))).is_err());
    }
}
