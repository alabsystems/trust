// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
fn fixture(kind: CallKind) -> Record {
    Record {
        owner: Definition { stable_crate_id: 7, local_hash: 11 },
        parameters: vec![2, 4],
        expressions: 9,
        source_hash: "md5=actual-source-file".into(),
        body: Body::Call {
            node: 5,
            definition: Definition { stable_crate_id: 13, local_hash: 17 },
            kind,
            generic_u64: kind == CallKind::RegisteredWrappingAdd,
            operands: vec![(0, Operand::Parameter(0)), (2, Operand::Parameter(1))],
        },
    }
}
#[test]
fn source_section_binds_owner_and_preserves_unavailable_without_authority() {
    let record = fixture(CallKind::RegisteredWrappingAdd);
    let wrong = Definition { local_hash: record.owner.local_hash + 1, ..record.owner };
    let bytes = encode_section(Some(&record), record.owner).unwrap();
    assert_eq!(decode_section(&bytes, record.owner).unwrap(), Some(record.clone()));
    assert!(encode_section(Some(&record), wrong).is_err());
    assert!(decode_section(&bytes, wrong).is_err());
    assert_eq!(encode_section(None, wrong).unwrap(), vec![0]);
    assert_eq!(decode_section(&[0], record.owner).unwrap(), None);
    for bytes in [&[][..], &[2][..], &[0, 0][..], &[1][..]] {
        assert!(decode_section(bytes, record.owner).is_err());
    }
}
#[test]
fn source_claim_roundtrip_preserves_owner_operands_and_call_kind() {
    for kind in [CallKind::OrdinaryCall, CallKind::RegisteredWrappingAdd] {
        let record = fixture(kind);
        let bytes = encode(&record).unwrap();
        assert_eq!(decode(&bytes).unwrap(), record);
        assert_eq!(encode(&decode(&bytes).unwrap()).unwrap(), bytes);
    }
    assert_ne!(
        encode(&fixture(CallKind::OrdinaryCall)).unwrap(),
        encode(&fixture(CallKind::RegisteredWrappingAdd)).unwrap()
    );
}
#[test]
fn source_claim_decoder_refuses_every_truncation_and_unknown_framing() {
    let bytes = encode(&fixture(CallKind::RegisteredWrappingAdd)).unwrap();
    for end in 0..bytes.len() {
        assert!(decode(&bytes[..end]).is_err(), "prefix {end}");
    }
    let mut wrong = bytes.clone();
    wrong[8..12].copy_from_slice(&2u32.to_le_bytes());
    assert!(decode(&wrong).is_err());
    let mut extra = bytes;
    extra.push(0);
    assert!(decode(&extra).is_err());
    assert!(decode(&vec![0; MAX_BYTES + 1]).is_err());
}
#[test]
fn source_claim_wire_decoder_rejects_malformed_fields() {
    let record = fixture(CallKind::RegisteredWrappingAdd);
    let bytes = encode(&record).unwrap();
    // Offsets follow the actual fixed-width fields and this fixture's
    // declared source-hash length, rather than scanning for byte patterns.
    let params = 8 + 4 + 16 + 1;
    let population = params + 4 * record.parameters.len();
    let hash_length = population + 4;
    let hash_start = hash_length + 4;
    let body = hash_start + record.source_hash.len();
    let generic = body + 1 + 4 + 16;
    let first = generic + 1;
    let second = first + 4 + 1 + 4;
    let mutants: Vec<(usize, Vec<u8>)> = vec![
        (0, vec![0]),                              // magic
        (params - 1, vec![3]),                     // unsupported parameter count
        (params + 4, 2u32.to_le_bytes().to_vec()), // duplicate parameter
        (population, 65u32.to_le_bytes().to_vec()),
        (hash_length, 257u32.to_le_bytes().to_vec()),
        (hash_start, vec![255]),                  // invalid UTF8
        (body, vec![3]),                          // unknown operation
        (body + 1, 9u32.to_le_bytes().to_vec()),  // out-of-range node
        (generic, vec![2]),                       // noncanonical Boolean
        (generic, vec![0]),                       // intrinsic lost substitution
        (first + 4, vec![2]),                     // unknown operand
        (first + 5, 2u32.to_le_bytes().to_vec()), // parameter out of scope
        (second, 0u32.to_le_bytes().to_vec()),    // aliased expression node
    ];
    for (offset, value) in mutants {
        let mut wrong = bytes.clone();
        wrong[offset..offset + value.len()].copy_from_slice(&value);
        assert!(decode(&wrong).is_err(), "malformed field at {offset}");
    }
}
#[test]
fn source_claim_literal_boundaries_and_single_parameter_roundtrip() {
    for literal in [0, u64::MAX] {
        let mut record = fixture(CallKind::OrdinaryCall);
        record.parameters = vec![2];
        record.body = Body::Operand { node: 0, value: Operand::Literal(literal) };
        assert_eq!(decode(&encode(&record).unwrap()).unwrap(), record);
        record.body = Body::Operand { node: 0, value: Operand::Parameter(0) };
        assert_eq!(decode(&encode(&record).unwrap()).unwrap(), record);
    }
}
#[test]
fn source_claim_refuses_aliases_out_of_telescope_nodes_and_generic_flags() {
    let good = fixture(CallKind::RegisteredWrappingAdd);
    let mut wrong = good.clone();
    wrong.parameters[1] = wrong.parameters[0];
    assert!(encode(&wrong).is_err());
    let mut wrong = good.clone();
    if let Body::Call { operands, .. } = &mut wrong.body {
        operands[1].1 = Operand::Parameter(2);
    }
    assert!(encode(&wrong).is_err());
    let mut wrong = good.clone();
    if let Body::Call { operands, .. } = &mut wrong.body {
        operands[1].0 = operands[0].0;
    }
    assert!(encode(&wrong).is_err());
    let mut wrong = good;
    if let Body::Call { generic_u64, .. } = &mut wrong.body {
        *generic_u64 = false;
    }
    assert!(encode(&wrong).is_err());
}
