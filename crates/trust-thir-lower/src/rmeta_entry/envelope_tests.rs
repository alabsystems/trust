use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Producer, Ty, ValueId,
};

use crate::rmeta_entry::{
    ENTRY_SCHEMA, EVIDENCE_SCHEMA, EntryBinding, EntryDecodeError, Evidence, decode_entry,
    decode_entry_for_overflow, decode_evidence, encode_evidence, frame_entry,
};

// These offsets are the schema-6 wire contract, not pointers into an implementation struct.
const HEADER: usize = 56;
const MODE: usize = HEADER + 16;
const MODULE_DIGEST: usize = MODE + 1;
const MODULE_LENGTH: usize = MODULE_DIGEST + 32;

fn module() -> Module {
    let mut m = Module::new("schema6_mode_control");
    let signature = m
        .intern_func_type(FuncTy {
            params: vec![Ty::U32],
            returns: vec![Ty::U32],
            is_vararg: false,
            abi: None,
        })
        .expect("fixture signature");
    let mut body = Function::new(FuncId::new(0), "actual_identity", signature, BlockId::new(0))
        .with_producer(Producer::TRust);
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U32);
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    body.blocks.push(block);
    m.try_add_function(body).expect("fixture body");
    m
}

fn frame(mode: bool) -> Vec<u8> {
    frame_entry(
        &module(),
        EntryBinding { stable_crate_id: 7, local_hash: 11 },
        mode,
        &encode_evidence(&Evidence::default()),
    )
    .expect("fixture frame")
}

// A hostile writer can recompute the public hash. Semantic mode checks must still refuse.
fn reseal(bytes: &mut [u8]) {
    let mut preimage = bytes[..16].to_vec();
    preimage.extend_from_slice(&bytes[HEADER..]);
    let digest =
        trust_ir::proof::ProofDigest::sha256_domain("trust.rmeta.entry-envelope.v1", &preimage);
    bytes[16..48].copy_from_slice(&digest.bytes);
}

#[test]
fn both_explicit_modes_roundtrip_and_opposite_consumer_modes_refuse() {
    let off = frame(false);
    let on = frame(true);
    assert_ne!(off, on);
    let a = decode_entry(&off).expect("checks off decodes");
    let b = decode_entry(&on).expect("checks on decodes");
    assert!(!a.overflow_checks);
    assert!(b.overflow_checks);
    assert_eq!(a.module, b.module);
    assert_eq!(a.digest, b.digest);
    assert_eq!(a.digest, a.module.stable_digest().bytes);
    assert_eq!(a.evidence, b.evidence);
    assert_ne!(a.content_digest, b.content_digest);
    for mode in [false, true] {
        let bytes = frame(mode);
        assert!(decode_entry_for_overflow(&bytes, mode).is_ok());
        assert_eq!(
            decode_entry_for_overflow(&bytes, !mode).expect_err("mode mismatch"),
            EntryDecodeError::OverflowMode { producer: mode, consumer: !mode },
        );
    }
}

#[test]
fn every_payload_byte_including_binding_mode_and_evidence_is_integrity_bound() {
    let good = frame(true);
    for at in HEADER..good.len() {
        let mut bad = good.clone();
        bad[at] ^= 1;
        assert_eq!(
            decode_entry(&bad).expect_err("altered payload"),
            EntryDecodeError::EnvelopeDigest,
            "unbound payload byte {at}",
        );
    }
    for at in 16..48 {
        let mut bad = good.clone();
        bad[at] ^= 1;
        assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::EnvelopeDigest);
    }
}

#[test]
fn resealed_noncanonical_mode_and_real_consumer_mismatch_still_refuse() {
    let mut bad = frame(true);
    bad[MODE] = 2;
    reseal(&mut bad);
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::OverflowByte(2));
    bad[MODE] = 0;
    reseal(&mut bad);
    assert!(!decode_entry(&bad).expect("canonical false mode").overflow_checks);
    assert_eq!(
        decode_entry_for_overflow(&bad, true).unwrap_err(),
        EntryDecodeError::OverflowMode { producer: false, consumer: true },
    );
}

#[test]
fn resealing_cannot_replace_the_independent_module_digest_check() {
    let mut bad = frame(true);
    bad[MODULE_DIGEST] ^= 1;
    reseal(&mut bad);
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::Digest);
}

#[test]
fn all_strict_prefixes_overflowed_lengths_and_trailing_bytes_refuse() {
    let good = frame(true);
    for cut in 0..good.len() {
        assert!(decode_entry(&good[..cut]).is_err(), "prefix {cut}");
    }
    let mut bad = good.clone();
    bad.push(0);
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::TrailingBytes(1));
    for length_at in [48, MODULE_LENGTH] {
        let mut bad = good.clone();
        bad[length_at..length_at + 8].copy_from_slice(&u64::MAX.to_le_bytes());
        if length_at != 48 {
            reseal(&mut bad);
        }
        assert!(matches!(
            decode_entry(&bad),
            Err(EntryDecodeError::Truncated(_) | EntryDecodeError::LengthOverflow(_))
        ));
    }
    let module_len =
        u64::from_le_bytes(good[MODULE_LENGTH..MODULE_LENGTH + 8].try_into().unwrap()) as usize;
    let evidence_len_at = MODULE_LENGTH + 8 + module_len;
    let mut bad = good;
    bad[evidence_len_at..evidence_len_at + 8].copy_from_slice(&u64::MAX.to_le_bytes());
    reseal(&mut bad);
    assert!(matches!(
        decode_entry(&bad),
        Err(EntryDecodeError::Truncated(_) | EntryDecodeError::LengthOverflow(_))
    ));
}

#[test]
fn an_inner_trailing_byte_is_refused_even_after_resealing() {
    let mut bad = frame(false);
    bad.push(0);
    let payload_len = bad.len() - HEADER;
    bad[48..56].copy_from_slice(&(payload_len as u64).to_le_bytes());
    reseal(&mut bad);
    assert_eq!(decode_entry(&bad).unwrap_err(), EntryDecodeError::TrailingBytes(1));
}

#[test]
fn old_entry_schemas_refuse_and_the_complete_evidence_schema_is_unchanged() {
    assert_eq!(ENTRY_SCHEMA, 6);
    assert_eq!(EVIDENCE_SCHEMA, 4);
    let good = frame(true);
    for schema in 0u32..6 {
        let mut old = good.clone();
        old[8..12].copy_from_slice(&schema.to_le_bytes());
        assert_eq!(decode_entry(&old).unwrap_err(), EntryDecodeError::Schema(schema));
    }
    let mut evidence = Evidence::default();
    evidence.arg_count = 3;
    evidence.arg_enum = vec![true, false, true];
    let bytes = encode_evidence(&evidence);
    let framed =
        frame_entry(&module(), EntryBinding { stable_crate_id: 7, local_hash: 11 }, false, &bytes)
            .unwrap();
    assert_eq!(decode_entry(&framed).unwrap().evidence, bytes);
}

#[test]
fn schema_errors_name_the_separate_entry_and_evidence_expectations() {
    let mut old_entry = frame(true);
    old_entry[8..12].copy_from_slice(&4u32.to_le_bytes());
    assert_eq!(decode_entry(&old_entry).unwrap_err().to_string(), "schema(4, expected 6)");
    let mut old_evidence = encode_evidence(&Evidence::default());
    old_evidence[8..12].copy_from_slice(&3u32.to_le_bytes());
    assert_eq!(decode_evidence(&old_evidence).unwrap_err(), EntryDecodeError::EvidenceSchema(3),);
    assert_eq!(
        decode_evidence(&old_evidence).unwrap_err().to_string(),
        "evidence-schema(3, expected 4)",
    );
}
