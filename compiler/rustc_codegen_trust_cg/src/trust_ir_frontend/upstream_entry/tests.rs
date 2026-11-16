use super::*;

#[test]
fn candidate_lookup_cannot_substitute_another_actual_stable_identity() {
    assert!(check_stable_identity((11, 22), (11, 22), 11).is_ok());
    for (hash, krate) in [((11, 23), 11), ((12, 22), 12), ((11, 22), 12)] {
        assert_eq!(check_stable_identity((11, 22), hash, krate).unwrap_err().check, "callee");
    }
}

fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    }
}

#[test]
fn target_mismatch_is_refused_and_never_restamped() {
    let wanted = target();
    let mut module = Module::new("target_control");
    assert_eq!(check_target(&module, &wanted).unwrap_err().check, "target");
    module.target_info = Some(wanted.clone());
    assert!(check_target(&module, &wanted).is_ok());
    for actual in [
        trust_ir::TargetInfo { triple: "aarch64-unknown-linux-gnu".into(), ..wanted.clone() },
        trust_ir::TargetInfo { pointer_size: 4, ..wanted.clone() },
        trust_ir::TargetInfo { endianness: Endianness::Big, ..wanted.clone() },
        trust_ir::TargetInfo { struct_passing: StructPassingPolicy::NativeC, ..wanted.clone() },
    ] {
        module.target_info = Some(actual.clone());
        assert!(check_target(&module, &wanted).is_err());
        assert_eq!(module.target_info, Some(actual));
    }
}

#[test]
fn complete_signature_mismatch_refuses_even_at_equal_arity_and_width() {
    let expected =
        FuncTy { params: vec![Ty::U32], returns: vec![Ty::U32], is_vararg: false, abi: None };
    assert!(
        check_signature_data(&expected, CallingConv::Rust, &expected, CallingConv::Rust).is_ok()
    );
    for actual in [
        FuncTy { params: vec![Ty::I32], ..expected.clone() },
        FuncTy { returns: vec![Ty::I32], ..expected.clone() },
        FuncTy { returns: vec![], ..expected.clone() },
        FuncTy { returns: vec![Ty::Never], ..expected.clone() },
        FuncTy { is_vararg: true, ..expected.clone() },
    ] {
        assert_eq!(
            check_signature_data(&actual, CallingConv::Rust, &expected, CallingConv::Rust)
                .unwrap_err()
                .check,
            "signature"
        );
    }
    assert!(check_signature_data(&expected, CallingConv::C, &expected, CallingConv::Rust).is_err());
}

#[test]
fn digest_mode_and_schema_failures_keep_their_named_checks() {
    assert_eq!(decode_error(EntryDecodeError::Digest).check, "digest");
    assert_eq!(decode_error(EntryDecodeError::EnvelopeDigest).check, "digest");
    assert_eq!(decode_error(EntryDecodeError::OverflowByte(2)).check, "mode");
    assert_eq!(
        decode_error(EntryDecodeError::OverflowMode { producer: false, consumer: true }).check,
        "mode"
    );
    assert_eq!(decode_error(EntryDecodeError::EvidenceSchema(3)).check, "schema");
    assert_eq!(
        Refusal::new("effects", "removed source call").frontend("f").class(),
        super::super::RefusalClass::EffectNotConserved
    );
    assert_eq!(
        Refusal::new("absent", "compiled without producer").frontend("f").class(),
        super::super::RefusalClass::UpstreamBody
    );
}

#[test]
fn d17_strict_condition_unchanged_for_upstream_bodies() {
    for (verification, configured, accepted) in [
        (false, "strict", true),
        (false, "allow-unknown", false),
        (false, "off", false),
        (true, "strict", true),
        (true, "allow-unknown", true),
        (true, "off", false),
    ] {
        assert_eq!(
            require_strict(instance_assembly::strict_gate_from(verification, configured)).is_ok(),
            accepted
        );
    }
}
