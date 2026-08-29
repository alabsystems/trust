// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The acceptance gate: differential against the incumbent `hmac` crate.**
//!
//! `trust-cache` and `trust-buildcache` seal every cache entry with an
//! HMAC-SHA256 tag written to disk. A disagreement with the incumbent would not
//! error — it would silently invalidate every sealed entry written by any tool
//! built before the swap, and (in `trust-buildcache`) make `verify_entry`
//! return `Ok(false)`, which the caller treats as corruption.
//!
//! This file must be deleted along with the `hmac`/`sha2` dev-dependencies on
//! the day the `[patch.crates-io]` redirect lands.

use hmac::Mac as _;
use trust_hmac::Mac as _;

type TheirsSha256 = hmac::Hmac<sha2::Sha256>;
type TheirsSha512 = hmac::Hmac<sha2::Sha512>;
type OursSha256 = trust_hmac::Hmac<trust_sha2::Sha256>;
type OursSha512 = trust_hmac::Hmac<trust_sha2::Sha512>;

/// SplitMix64 — deterministic, dependency-free.
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

fn ours_256(key: &[u8], data: &[u8]) -> String {
    let mut mac = OursSha256::new_from_slice(key).expect("any key length");
    mac.update(data);
    format!("{:x}", mac.finalize().into_bytes())
}

fn theirs_256(key: &[u8], data: &[u8]) -> String {
    let mut mac = TheirsSha256::new_from_slice(key).expect("any key length");
    mac.update(data);
    format!("{:x}", mac.finalize().into_bytes())
}

fn ours_512(key: &[u8], data: &[u8]) -> String {
    let mut mac = OursSha512::new_from_slice(key).expect("any key length");
    mac.update(data);
    format!("{:x}", mac.finalize().into_bytes())
}

fn theirs_512(key: &[u8], data: &[u8]) -> String {
    let mut mac = TheirsSha512::new_from_slice(key).expect("any key length");
    mac.update(data);
    format!("{:x}", mac.finalize().into_bytes())
}

/// Every key length from 0 to 200 crosses both block-size transitions (64 for
/// SHA-256, 128 for SHA-512) and both hash-the-key branches.
#[test]
fn every_key_length_to_200_agrees() {
    let mut rng = Rng(0x40ac_0001);
    for key_length in 0..=200usize {
        let key = rng.bytes(key_length);
        let data_length = rng.below(400);
        let data = rng.bytes(data_length);
        assert_eq!(
            ours_256(&key, &data),
            theirs_256(&key, &data),
            "HMAC-SHA256 differs at key length {key_length}"
        );
        assert_eq!(
            ours_512(&key, &data),
            theirs_512(&key, &data),
            "HMAC-SHA512 differs at key length {key_length}"
        );
    }
}

/// Every message length from 0 to 400, with the 32-byte key both consumers use.
#[test]
fn every_message_length_to_400_agrees() {
    let key: Vec<u8> = (0..32).map(|i| ((i * 37 + 11) & 0xff) as u8).collect();
    let mut rng = Rng(0x40ac_0002);
    for length in 0..=400usize {
        let data = rng.bytes(length);
        assert_eq!(
            ours_256(&key, &data),
            theirs_256(&key, &data),
            "HMAC-SHA256 differs at message length {length}"
        );
        assert_eq!(
            ours_512(&key, &data),
            theirs_512(&key, &data),
            "HMAC-SHA512 differs at message length {length}"
        );
    }
}

/// Incremental feeding with randomized split points, against the incumbent's
/// own incremental API.
#[test]
fn randomized_chunkings_agree() {
    let mut rng = Rng(0x40ac_0003);

    for _ in 0..300 {
        let key_length = rng.below(80);
        let key = rng.bytes(key_length);
        let length = rng.below(600);
        let data = rng.bytes(length);

        let split_count = rng.below(10);
        let mut splits: Vec<usize> = (0..split_count).map(|_| rng.below(length + 1)).collect();
        splits.sort_unstable();

        let mut ours = OursSha256::new_from_slice(&key).expect("any key length");
        let mut theirs = TheirsSha256::new_from_slice(&key).expect("any key length");
        let mut position = 0;
        for &split in &splits {
            if split > position {
                trust_hmac::Mac::update(&mut ours, &data[position..split]);
                hmac::Mac::update(&mut theirs, &data[position..split]);
                position = split;
            }
        }
        trust_hmac::Mac::update(&mut ours, &data[position..]);
        hmac::Mac::update(&mut theirs, &data[position..]);

        assert_eq!(
            format!("{:x}", ours.finalize().into_bytes()),
            format!("{:x}", theirs.finalize().into_bytes()),
            "HMAC-SHA256 incremental differs: key {} bytes, message {length}, splits {splits:?}",
            key.len()
        );
    }
}

/// `verify_slice` must agree with the incumbent on acceptance AND rejection,
/// including the wrong-length case.
#[test]
fn verify_slice_agrees() {
    let mut rng = Rng(0x40ac_0004);

    for _ in 0..200 {
        let key_length = rng.below(100);
        let key = rng.bytes(key_length);
        let data_length = rng.below(300);
        let data = rng.bytes(data_length);

        let mut reference = TheirsSha256::new_from_slice(&key).expect("any key length");
        reference.update(&data);
        let tag = reference.finalize().into_bytes().to_vec();

        // Correct tag: both accept.
        let mut ours = OursSha256::new_from_slice(&key).expect("any key length");
        trust_hmac::Mac::update(&mut ours, &data);
        assert!(ours.verify_slice(&tag).is_ok(), "our verify rejected the incumbent's own tag");

        let mut theirs = TheirsSha256::new_from_slice(&key).expect("any key length");
        theirs.update(&data);
        assert!(theirs.verify_slice(&tag).is_ok());

        // Corrupted tag: both reject.
        let mut corrupted = tag.clone();
        let index = rng.below(corrupted.len());
        corrupted[index] ^= 1 << rng.below(8);

        let mut ours = OursSha256::new_from_slice(&key).expect("any key length");
        trust_hmac::Mac::update(&mut ours, &data);
        let ours_verdict = ours.verify_slice(&corrupted).is_ok();

        let mut theirs = TheirsSha256::new_from_slice(&key).expect("any key length");
        theirs.update(&data);
        let theirs_verdict = theirs.verify_slice(&corrupted).is_ok();

        assert_eq!(ours_verdict, theirs_verdict, "verify_slice verdicts diverge on a corrupt tag");
        assert!(!ours_verdict);

        // Wrong-length tag: both reject.
        let mut ours = OursSha256::new_from_slice(&key).expect("any key length");
        trust_hmac::Mac::update(&mut ours, &data);
        let ours_verdict = ours.verify_slice(&tag[..16]).is_ok();

        let mut theirs = TheirsSha256::new_from_slice(&key).expect("any key length");
        theirs.update(&data);
        let theirs_verdict = theirs.verify_slice(&tag[..16]).is_ok();

        assert_eq!(ours_verdict, theirs_verdict, "verify_slice verdicts diverge on a short tag");
        assert!(!ours_verdict);
    }
}

/// The two consumers' exact byte streams, run through both implementations.
///
/// If these disagree, every sealed cache entry on disk becomes unreadable at
/// the moment of the swap — a silent, tree-wide invalidation.
#[test]
fn consumer_byte_streams_agree() {
    // trust_cache::integrity::compute_hmac — a 32-byte key over one blob.
    let key: [u8; 32] = [0x5a; 32];
    let payload = b"{\"schema\":\"trust.cache.v1\",\"entries\":3}";
    assert_eq!(ours_256(&key, payload), theirs_256(&key, payload));

    // trust_buildcache::integrity::update_entry_hmac — per-file framing:
    // name || 0x00 || 8-byte LE length || contents, streamed in 64 KiB reads.
    let files: &[(&str, &[u8])] = &[
        ("rlib", &[0xab; 70_000]),
        ("rmeta", &[0xcd; 130]),
        ("depfile", b""),
        ("certificate.json", b"{\"verdict\":\"Proved\"}"),
        ("metadata.json", &[0x11; 65_536]),
    ];

    let mut ours = OursSha256::new_from_slice(&key).expect("any key length");
    let mut theirs = TheirsSha256::new_from_slice(&key).expect("any key length");
    for (name, contents) in files {
        trust_hmac::Mac::update(&mut ours, name.as_bytes());
        trust_hmac::Mac::update(&mut ours, &[0]);
        trust_hmac::Mac::update(&mut ours, &(contents.len() as u64).to_le_bytes());
        hmac::Mac::update(&mut theirs, name.as_bytes());
        hmac::Mac::update(&mut theirs, &[0]);
        hmac::Mac::update(&mut theirs, &(contents.len() as u64).to_le_bytes());

        // The real loop reads into a 64 KiB buffer, so a long file arrives in
        // several pieces and the last piece is short.
        for piece in contents.chunks(64 * 1024) {
            trust_hmac::Mac::update(&mut ours, piece);
            hmac::Mac::update(&mut theirs, piece);
        }
    }

    assert_eq!(
        format!("{:x}", ours.finalize().into_bytes()),
        format!("{:x}", theirs.finalize().into_bytes()),
        "the build-cache seal disagrees with the incumbent"
    );

    // trust_buildcache::integrity::compatibility_key — SHA-256 of a fixed
    // label, used as the HMAC key. Both halves of the swap in one place.
    let label = b"trust-buildcache/integrity/v2\0non-secret-cross-tool-key";
    let ours_key: [u8; 32] = <trust_sha2::Sha256 as trust_sha2::Digest>::digest(label).into();
    let theirs_key = {
        let mut key = [0u8; 32];
        key.copy_from_slice(&<sha2::Sha256 as sha2::Digest>::digest(label));
        key
    };
    assert_eq!(ours_key, theirs_key, "the derived compatibility key differs");
    assert_eq!(ours_256(&ours_key, payload), theirs_256(&theirs_key, payload));
}
