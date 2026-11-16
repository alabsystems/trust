// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

#[test]
fn kernel_mapping_decoder_refuses_short_overflow_and_ambiguous_names() {
    assert!(parse_region(&[0; 10]).is_err());
    let mut record = [0u8; 1272];
    record[80..88].copy_from_slice(&0x1000u64.to_ne_bytes());
    record[88..96].copy_from_slice(&0x2000u64.to_ne_bytes());
    record[0..4].copy_from_slice(&5u32.to_ne_bytes());
    record[96..100].copy_from_slice(&17u32.to_ne_bytes());
    record[104..112].copy_from_slice(&1234u64.to_ne_bytes());
    let name = b"/original/native-image";
    record[248..248 + name.len()].copy_from_slice(name);
    let decoded = parse_region(&record).unwrap();
    assert_eq!(
        (decoded.start, decoded.bytes, decoded.protection, decoded.inode),
        (0x1000, 0x2000, 5, 1234)
    );
    record[80..88].copy_from_slice(&u64::MAX.to_ne_bytes());
    assert!(parse_region(&record).is_err());
    record[80..88].copy_from_slice(&0x1000u64.to_ne_bytes());
    record[248..].fill(0);
    assert!(parse_region(&record).is_err(), "a file-backed record needs its complete kernel name");
    record[248..].fill(b'x');
    assert!(parse_region(&record).is_err());
}
