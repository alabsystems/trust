// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The acceptance gate: differential against the incumbent `sha2` crate.**
//!
//! Every certificate identity, build-cache key and MIR fingerprint in this tree
//! is a SHA-256 produced today by `sha2`. Swapping the implementation is only
//! safe if the two agree on *every* input the tree can present — a disagreement
//! on some length class would silently re-key the entire cache and re-name
//! every certificate, with no error anywhere.
//!
//! So this compares the two implementations directly, while both still exist.
//! It is the file that must be deleted (with the `sha2` dev-dependency) on the
//! day the `[patch.crates-io]` redirect lands, and until then it is the only
//! test here whose failure is a hard blocker on integration.
//!
//! Coverage: every length from 0 to 600 bytes for all four digest widths,
//! degenerate content at every boundary length, multi-block inputs to 1 MB,
//! randomized chunk splits, the rendered hex form (which is what the call sites
//! actually consume), and the exact argument shapes measured at those sites.

use sha2::Digest as _;
use trust_sha2::Digest as _;

/// SplitMix64. Deterministic so a failure is reproducible; the crate has no
/// dependencies and a test may not add one.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        if bound == 0 { 0 } else { (self.next_u64() % bound as u64) as usize }
    }

    fn bytes(&mut self, length: usize) -> Vec<u8> {
        (0..length).map(|_| (self.next_u64() >> 24) as u8).collect()
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("String write cannot fail");
    }
    out
}

/// One-shot agreement for all four widths at a single input.
fn assert_one_shot_agrees(data: &[u8], label: &str) {
    let expected = sha2::Sha256::digest(data);
    assert_eq!(
        hex(trust_sha2::Sha256::digest(data).as_ref()),
        hex(&expected),
        "SHA-256 differs from the incumbent ({label})"
    );
    assert_eq!(
        hex(trust_sha2::NativeSha256::digest(data).as_ref()),
        hex(&expected),
        "native SHA-256 differs from the incumbent ({label})"
    );
    assert_eq!(
        hex(trust_sha2::Sha512::digest(data).as_ref()),
        hex(&sha2::Sha512::digest(data)),
        "SHA-512 differs from the incumbent ({label})"
    );
    assert_eq!(
        hex(trust_sha2::Sha224::digest(data).as_ref()),
        hex(&sha2::Sha224::digest(data)),
        "SHA-224 differs from the incumbent ({label})"
    );
    assert_eq!(
        hex(trust_sha2::Sha384::digest(data).as_ref()),
        hex(&sha2::Sha384::digest(data)),
        "SHA-384 differs from the incumbent ({label})"
    );
}

/// Exhaustive over length: 0..=600 covers every padding class of both families
/// several times over (SHA-256 blocks at 64, SHA-512 at 128).
#[test]
fn every_length_to_600_agrees() {
    let mut rng = Rng(0x5a2_0001);
    for length in 0..=600usize {
        let data = rng.bytes(length);
        assert_one_shot_agrees(&data, &format!("length {length}"));
    }
}

/// All-zero, all-ones and high-bit-set inputs at every boundary length: content
/// patterns that maximize the chance of a carry or rotate mistake surviving
/// random data.
#[test]
fn degenerate_content_agrees() {
    for length in [0usize, 1, 55, 56, 63, 64, 65, 111, 112, 119, 120, 127, 128, 129, 255, 256] {
        for fill in [0x00u8, 0xff, 0x80, 0x7f] {
            let data = vec![fill; length];
            assert_one_shot_agrees(&data, &format!("length {length} filled {fill:#04x}"));
        }
    }
}

/// Multi-block inputs, including one past any plausible internal buffer.
#[test]
fn large_inputs_agree() {
    let mut rng = Rng(0x5a2_0002);
    for _ in 0..64 {
        let length = rng.below(4096);
        let data = rng.bytes(length);
        assert_one_shot_agrees(&data, &format!("random length {length}"));
    }

    let mut rng = Rng(0x5a2_0003);
    let data = rng.bytes(1_000_003);
    assert_one_shot_agrees(&data, "1,000,003 bytes");
}

/// Incremental feeding with randomized split points, against the incumbent's
/// own incremental API. This is the path every streaming caller in the tree
/// uses, and no one-shot comparison can see a bug in it.
#[test]
fn randomized_chunkings_agree() {
    let mut rng = Rng(0x5a2_0004);

    for _ in 0..400 {
        let length = rng.below(700);
        let data = rng.bytes(length);

        let split_count = rng.below(12);
        let mut splits: Vec<usize> = (0..split_count).map(|_| rng.below(length + 1)).collect();
        splits.sort_unstable();

        let mut ours = trust_sha2::Sha256::new();
        let mut native = trust_sha2::NativeSha256::new();
        let mut theirs = sha2::Sha256::new();
        let mut position = 0;
        for &split in &splits {
            if split > position {
                ours.update(&data[position..split]);
                native.update(&data[position..split]);
                theirs.update(&data[position..split]);
                position = split;
            }
        }
        ours.update(&data[position..]);
        native.update(&data[position..]);
        theirs.update(&data[position..]);
        let expected = theirs.finalize();
        assert_eq!(
            hex(ours.finalize().as_ref()),
            hex(&expected),
            "SHA-256 incremental differs: length {length}, splits {splits:?}"
        );
        assert_eq!(
            hex(native.finalize().as_ref()),
            hex(&expected),
            "native SHA-256 incremental differs: length {length}, splits {splits:?}"
        );

        let mut ours = trust_sha2::Sha512::new();
        let mut theirs = sha2::Sha512::new();
        let mut position = 0;
        for &split in &splits {
            if split > position {
                ours.update(&data[position..split]);
                theirs.update(&data[position..split]);
                position = split;
            }
        }
        ours.update(&data[position..]);
        theirs.update(&data[position..]);
        assert_eq!(
            hex(ours.finalize().as_ref()),
            hex(&theirs.finalize()),
            "SHA-512 incremental differs: length {length}, splits {splits:?}"
        );
    }
}

/// The **rendered** form must match, not just the bytes.
///
/// `format!("{:x}", digest)` is what the call sites store, and the incumbent's
/// `LowerHex` comes from `generic-array`, which has its own opinions (precision
/// truncates; width and fill are ignored because it writes with `write_str`).
/// A byte-identical digest that renders differently still changes every
/// identity string in the tree.
#[test]
fn lower_hex_rendering_matches_the_incumbent() {
    let mut rng = Rng(0x5a2_0005);
    for _ in 0..64 {
        let length = rng.below(300);
        let data = rng.bytes(length);

        let ours = trust_sha2::Sha256::digest(&data);
        let theirs = sha2::Sha256::digest(&data);
        assert_eq!(format!("{ours:x}"), format!("{theirs:x}"));
        assert_eq!(format!("{ours:X}"), format!("{theirs:X}"));
        // Precision truncation, including the odd-digit and zero cases.
        assert_eq!(format!("{ours:.16x}"), format!("{theirs:.16x}"));
        assert_eq!(format!("{ours:.7x}"), format!("{theirs:.7x}"));
        assert_eq!(format!("{ours:.0x}"), format!("{theirs:.0x}"));
        assert_eq!(format!("{ours:.64x}"), format!("{theirs:.64x}"));

        let ours = trust_sha2::Sha512::digest(&data);
        let theirs = sha2::Sha512::digest(&data);
        assert_eq!(format!("{ours:x}"), format!("{theirs:x}"));
    }
}

/// The exact call shapes measured at real sites, run through both
/// implementations. Not a shape test — a *value* test on the shapes.
#[test]
fn measured_call_shapes_agree() {
    // trust_buildcache::key::hash_bytes (deleted by T11) — 8-byte length
    // framing, BY VALUE.
    let label: &[u8] = b"rustc_version";
    let value: &[u8] = b"1.99.0-dev";

    let mut ours = trust_sha2::Sha256::new();
    ours.update((label.len() as u64).to_le_bytes());
    ours.update(label);
    ours.update((value.len() as u64).to_le_bytes());
    ours.update(value);

    let mut theirs = sha2::Sha256::new();
    theirs.update((label.len() as u64).to_le_bytes());
    theirs.update(label);
    theirs.update((value.len() as u64).to_le_bytes());
    theirs.update(value);

    assert_eq!(hex(ours.finalize().as_ref()), hex(&theirs.finalize()));

    // trust_types::digest::stable_sha256_hex_parts — iterating `&[&[u8]]`
    // yields `&&[u8]`, which only typechecks through the blanket AsRef impl.
    let parts: &[&[u8]] = &[b"alpha", b"", b"beta", b"gamma"];
    let mut ours = trust_sha2::Sha256::new();
    let mut theirs = sha2::Sha256::new();
    for part in parts {
        ours.update(part);
        theirs.update(part);
    }
    assert_eq!(hex(ours.finalize().as_ref()), hex(&theirs.finalize()));

    // trust_cache::integrity::compute_cache_key (deleted by T11) — b"\x00"
    // separators.
    let mut ours = trust_sha2::Sha256::new();
    ours.update("exe-hash".as_bytes());
    ours.update(b"\x00");
    ours.update("hostname".as_bytes());
    let mut theirs = sha2::Sha256::new();
    theirs.update("exe-hash".as_bytes());
    theirs.update(b"\x00");
    theirs.update("hostname".as_bytes());
    assert_eq!(hex(ours.finalize().as_ref()), hex(&theirs.finalize()));

    // One-shot over an owned Vec and over a &Vec, both measured at call sites.
    let owned: Vec<u8> = b"{\"schema\":\"trust.report.ndjson.v2\"}".to_vec();
    assert_eq!(
        hex(trust_sha2::Sha256::digest(owned.clone()).as_ref()),
        hex(&sha2::Sha256::digest(&owned))
    );
    assert_eq!(
        hex(trust_sha2::Sha256::digest(&owned).as_ref()),
        hex(&sha2::Sha256::digest(owned.as_slice()))
    );

    // trust_report::json_output::DigestWriter — a `&mut Sha256` behind
    // `std::io::Write`, fed by serde in whatever chunk sizes it chooses.
    struct DigestWriter<'a>(&'a mut trust_sha2::Sha256);
    impl std::io::Write for DigestWriter<'_> {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.0.update(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    let payload = b"{\"record_type\":\"function\",\"name\":\"trust::demo\"}";
    let mut hasher = trust_sha2::Sha256::new();
    {
        use std::io::Write as _;
        let mut writer = DigestWriter(&mut hasher);
        writer.write_all(&payload[..7]).unwrap();
        writer.write_all(&payload[7..]).unwrap();
    }
    assert_eq!(hex(hasher.finalize().as_ref()), hex(&sha2::Sha256::digest(payload)));
}
