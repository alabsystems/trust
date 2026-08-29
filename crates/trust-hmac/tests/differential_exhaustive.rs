// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Exhaustive differential against the incumbent `hmac` crate.**
//!
//! Companion to `differential_hmac.rs` (which samples randomly). This file is
//! the exhaustive half, organized around the one structural decision HMAC
//! makes — RFC 2104 §2, step 1:
//!
//! > *if the key is longer than B bytes, it is first hashed to L bytes; if it
//! > is shorter than B, it is padded with zeros to B.*
//!
//! `B` is the **block** size (64 for SHA-256, 128 for SHA-512), not the output
//! size, and confusing the two is the classic HMAC bug. It is also invisible
//! to RFC 4231's own vectors, whose long-key cases use a 131-byte key —
//! longer than both 32 and 64, so both rules hash it and agree. Only a key
//! whose length falls *between* the output size and the block size can tell
//! them apart, and neither consumer in this tree uses one. That gap is what
//! this file closes, exhaustively:
//!
//! * every key length 0..=200 (SHA-256: crosses 32, 64; SHA-512: crosses 64)
//!   and 0..=300 for SHA-512 (crosses 64 and 128), against deterministic key
//!   material;
//! * the three key classes named explicitly — shorter than B, exactly B,
//!   longer than B — each with every message length 0..=200;
//! * multi-megabyte messages under each key class;
//! * `update` split at every offset, for several message lengths, under each
//!   key class.
//!
//! A failure prints the key, the message and both tags.
//!
//! Deleted, with the `hmac`/`sha2` dev-dependencies, on the day the incumbent
//! leaves the graph.

use hmac::Mac as _;
use trust_hmac::Mac as _;
use trust_sha2::Digest as _;

type TheirsSha256 = hmac::Hmac<sha2::Sha256>;
type TheirsSha512 = hmac::Hmac<sha2::Sha512>;
type OursSha256 = trust_hmac::Hmac<trust_sha2::Sha256>;
type OursSha512 = trust_hmac::Hmac<trust_sha2::Sha512>;

/// FIPS 180-4 Table 1: the block size B that RFC 2104 §2 is written in terms of.
const B_SHA256: usize = 64;
const B_SHA512: usize = 128;

// ---------------------------------------------------------------------------
// Deterministic material and reporting
// ---------------------------------------------------------------------------

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(&mut out, "{byte:02x}").expect("String write cannot fail");
    }
    out
}

/// Deterministic key material: `key(n)[i] = (i*97 + 3) mod 256`. A prefix of a
/// longer key is the shorter key, so "key length 64" and "key length 65" differ
/// by exactly one appended byte — which is the discrimination the block-size
/// rule turns on.
fn key(length: usize) -> Vec<u8> {
    (0..length).map(|i| (i.wrapping_mul(97).wrapping_add(3)) as u8).collect()
}

/// Deterministic message material, distinct from the key pattern.
fn message(length: usize) -> Vec<u8> {
    (0..length).map(|i| (i.wrapping_mul(167).wrapping_add(13)) as u8).collect()
}

fn describe(bytes: &[u8]) -> String {
    if bytes.len() <= 96 {
        format!("{} bytes: {}", bytes.len(), hex(bytes))
    } else {
        format!(
            "{} bytes: {}...{} (first 48 and last 48)",
            bytes.len(),
            hex(&bytes[..48]),
            hex(&bytes[bytes.len() - 48..])
        )
    }
}

#[track_caller]
fn compare(algorithm: &str, recipe: &str, key: &[u8], data: &[u8], ours: &[u8], theirs: &[u8]) {
    if ours != theirs {
        panic!(
            "\n\
             ================ DIFFERENTIAL DISAGREEMENT ================\n\
             algorithm : {algorithm}\n\
             recipe    : {recipe}\n\
             key       : {}\n\
             message   : {}\n\
             trust-hmac: {}\n\
             hmac (inc): {}\n\
             ===========================================================\n",
            describe(key),
            describe(data),
            hex(ours),
            hex(theirs),
        );
    }
}

fn ours_256(key: &[u8], data: &[u8]) -> Vec<u8> {
    let mut mac = OursSha256::new_from_slice(key).expect("HMAC accepts any key length");
    trust_hmac::Mac::update(&mut mac, data);
    mac.finalize().into_bytes().as_ref().to_vec()
}

fn theirs_256(key: &[u8], data: &[u8]) -> Vec<u8> {
    let mut mac = TheirsSha256::new_from_slice(key).expect("HMAC accepts any key length");
    hmac::Mac::update(&mut mac, data);
    mac.finalize().into_bytes().to_vec()
}

fn ours_512(key: &[u8], data: &[u8]) -> Vec<u8> {
    let mut mac = OursSha512::new_from_slice(key).expect("HMAC accepts any key length");
    trust_hmac::Mac::update(&mut mac, data);
    mac.finalize().into_bytes().as_ref().to_vec()
}

fn theirs_512(key: &[u8], data: &[u8]) -> Vec<u8> {
    let mut mac = TheirsSha512::new_from_slice(key).expect("HMAC accepts any key length");
    hmac::Mac::update(&mut mac, data);
    mac.finalize().into_bytes().to_vec()
}

// ---------------------------------------------------------------------------
// 1. Every key length, exhaustively, across the block-size transition
// ---------------------------------------------------------------------------

/// Every key length from 0 to 300 inclusive, for both hashes.
///
/// The range is chosen to cross *every* threshold either rule could key on:
/// 28/32/48/64 (the four SHA-2 output sizes) and 64/128 (the two block sizes).
/// A implementation that hashed keys longer than `OUTPUT_SIZE` instead of
/// `BLOCK_SIZE` agrees with the correct one everywhere except the intervals
/// (32, 64] for SHA-256 and (64, 128] for SHA-512 — 32 and 64 lengths
/// respectively, all of which are inside this sweep.
#[test]
fn every_key_length_to_300_agrees() {
    let data = message(137);
    let mut checked = 0usize;
    for key_length in 0..=300usize {
        let k = key(key_length);
        let recipe = format!("key({key_length}), message(137)");
        compare("HMAC-SHA256", &recipe, &k, &data, &ours_256(&k, &data), &theirs_256(&k, &data));
        compare("HMAC-SHA512", &recipe, &k, &data, &ours_512(&k, &data), &theirs_512(&k, &data));
        checked += 2;
    }
    println!(
        "every_key_length_to_300: {checked} tags agree \
         (301 key lengths x 2 hashes; crosses B={B_SHA256} and B={B_SHA512})"
    );
}

/// The same sweep with the empty message and with a message that is exactly one
/// block — the two message shapes where an inner-hash padding bug and a
/// key-padding bug could cancel.
#[test]
fn every_key_length_with_degenerate_messages_agrees() {
    for &data_length in &[0usize, B_SHA256, B_SHA512] {
        let data = message(data_length);
        for key_length in 0..=200usize {
            let k = key(key_length);
            let recipe = format!("key({key_length}), message({data_length})");
            compare(
                "HMAC-SHA256",
                &recipe,
                &k,
                &data,
                &ours_256(&k, &data),
                &theirs_256(&k, &data),
            );
            compare(
                "HMAC-SHA512",
                &recipe,
                &k,
                &data,
                &ours_512(&k, &data),
                &theirs_512(&k, &data),
            );
        }
    }
    println!(
        "every_key_length_with_degenerate_messages: 201 key lengths x 3 messages x 2 hashes agree"
    );
}

// ---------------------------------------------------------------------------
// 2. The three key classes, named
// ---------------------------------------------------------------------------

/// Key lengths for SHA-256 labelled by their relation to B = 64.
/// The `(32, 64]` entries are the ones that discriminate BLOCK_SIZE from
/// OUTPUT_SIZE, and RFC 4231 contains none of them.
const KEY_CLASSES_SHA256: &[(&str, usize)] = &[
    ("shorter than B", 0),
    ("shorter than B", 1),
    ("shorter than B", 31),
    ("shorter than B (== OUTPUT_SIZE)", 32),
    ("shorter than B (discriminating)", 33),
    ("shorter than B (discriminating)", 63),
    ("EXACTLY B", 64),
    ("longer than B", 65),
    ("longer than B", 100),
    ("longer than B", 128),
    ("longer than B", 200),
];

/// Key lengths for SHA-512 labelled by their relation to B = 128. The
/// discriminating interval here is `(64, 128]`.
const KEY_CLASSES_SHA512: &[(&str, usize)] = &[
    ("shorter than B", 0),
    ("shorter than B", 1),
    ("shorter than B", 63),
    ("shorter than B (== OUTPUT_SIZE)", 64),
    ("shorter than B (discriminating)", 65),
    ("shorter than B (discriminating)", 127),
    ("EXACTLY B", 128),
    ("longer than B", 129),
    ("longer than B", 200),
    ("longer than B", 256),
];

/// Every message length 0..=200 under every named key class, both hashes.
#[test]
fn every_message_length_under_each_key_class_agrees() {
    let mut checked = 0usize;

    for (class, key_length) in KEY_CLASSES_SHA256 {
        let k = key(*key_length);
        for data_length in 0..=200usize {
            let data = message(data_length);
            let recipe =
                format!("SHA-256 key class '{class}' key({key_length}), message({data_length})");
            compare(
                "HMAC-SHA256",
                &recipe,
                &k,
                &data,
                &ours_256(&k, &data),
                &theirs_256(&k, &data),
            );
            checked += 1;
        }
    }

    for (class, key_length) in KEY_CLASSES_SHA512 {
        let k = key(*key_length);
        for data_length in 0..=200usize {
            let data = message(data_length);
            let recipe =
                format!("SHA-512 key class '{class}' key({key_length}), message({data_length})");
            compare(
                "HMAC-SHA512",
                &recipe,
                &k,
                &data,
                &ours_512(&k, &data),
                &theirs_512(&k, &data),
            );
            checked += 1;
        }
    }

    println!("every_message_length_under_each_key_class: {checked} tags agree");
}

/// The discriminating interval, on its own, spelled out.
///
/// For SHA-256 that is every key length in `(32, 64]`; for SHA-512 every length
/// in `(64, 128]`. If `trust-hmac` ever hashes long keys down using
/// `OUTPUT_SIZE` instead of `BLOCK_SIZE`, this is the only test in the suite
/// that is guaranteed to see it — a full RFC 4231 run stays green.
#[test]
fn the_block_size_discriminating_interval_agrees() {
    let data = message(73);

    for key_length in 33..=64usize {
        let k = key(key_length);
        compare(
            "HMAC-SHA256 (BLOCK_SIZE vs OUTPUT_SIZE discriminator)",
            &format!("key({key_length}) in (OUTPUT_SIZE=32, BLOCK_SIZE=64]"),
            &k,
            &data,
            &ours_256(&k, &data),
            &theirs_256(&k, &data),
        );
    }

    for key_length in 65..=128usize {
        let k = key(key_length);
        compare(
            "HMAC-SHA512 (BLOCK_SIZE vs OUTPUT_SIZE discriminator)",
            &format!("key({key_length}) in (OUTPUT_SIZE=64, BLOCK_SIZE=128]"),
            &k,
            &data,
            &ours_512(&k, &data),
            &theirs_512(&k, &data),
        );
    }

    // And the far side: a key one byte past B, which MUST be hashed.
    for (label, key_length, block) in
        [("SHA-256", B_SHA256 + 1, B_SHA256), ("SHA-512", B_SHA512 + 1, B_SHA512)]
    {
        let k = key(key_length);
        if label == "SHA-256" {
            compare(
                "HMAC-SHA256 (one byte past B)",
                &format!("key({key_length}), B={block}"),
                &k,
                &data,
                &ours_256(&k, &data),
                &theirs_256(&k, &data),
            );
            // The RFC's own equivalence: HMAC(K, m) with |K| > B equals
            // HMAC(H(K), m). Assert it against the incumbent, both sides.
            let hashed: [u8; 32] = trust_sha2::Sha256::digest(&k).into();
            assert_eq!(
                ours_256(&k, &data),
                ours_256(&hashed, &data),
                "RFC 2104 s2 step 1: HMAC(K,m) != HMAC(H(K),m) for |K| > B"
            );
            assert_eq!(theirs_256(&k, &data), theirs_256(&hashed, &data));
        } else {
            compare(
                "HMAC-SHA512 (one byte past B)",
                &format!("key({key_length}), B={block}"),
                &k,
                &data,
                &ours_512(&k, &data),
                &theirs_512(&k, &data),
            );
            let hashed: [u8; 64] = trust_sha2::Sha512::digest(&k).into();
            assert_eq!(ours_512(&k, &data), ours_512(&hashed, &data));
            assert_eq!(theirs_512(&k, &data), theirs_512(&hashed, &data));
        }
    }

    println!(
        "the_block_size_discriminating_interval: SHA-256 keys 33..=64 and \
         SHA-512 keys 65..=128 agree; the |K|>B equivalence holds on both sides"
    );
}

// ---------------------------------------------------------------------------
// 3. Multi-megabyte messages
// ---------------------------------------------------------------------------

fn large_message(seed: usize, length: usize) -> Vec<u8> {
    (0..length).map(|i| (i.wrapping_add(seed).wrapping_mul(167).wrapping_add(13)) as u8).collect()
}

/// Several multi-megabyte messages under each key class (one representative per
/// class, to keep the opt-level-0 binary's runtime honest).
#[test]
fn multi_megabyte_messages_agree() {
    for &length in &[1_048_576usize, 2_097_153, 3_000_001] {
        let data = large_message(length % 251, length);

        for &(class, key_length) in
            &[("shorter than B", 32usize), ("EXACTLY B", 64), ("longer than B", 100)]
        {
            let k = key(key_length);
            compare(
                "HMAC-SHA256",
                &format!("key class '{class}' key({key_length}), large_message({length})"),
                &k,
                &data,
                &ours_256(&k, &data),
                &theirs_256(&k, &data),
            );
        }

        for &(class, key_length) in
            &[("shorter than B", 64usize), ("EXACTLY B", 128), ("longer than B", 200)]
        {
            let k = key(key_length);
            compare(
                "HMAC-SHA512",
                &format!("key class '{class}' key({key_length}), large_message({length})"),
                &k,
                &data,
                &ours_512(&k, &data),
                &theirs_512(&k, &data),
            );
        }

        println!(
            "multi_megabyte_messages: {length} bytes agree under all 3 key classes x 2 hashes"
        );
    }
}

/// A multi-megabyte message fed in 64 KiB pieces — `trust_buildcache`'s real
/// read size — against the incumbent's single-`update` tag.
#[test]
fn multi_megabyte_streamed_agrees() {
    for &length in &[1_048_576usize, 3_000_001] {
        let data = large_message(7, length);
        for &key_length in &[32usize, 64, 100] {
            let k = key(key_length);

            let mut ours = OursSha256::new_from_slice(&k).expect("any key length");
            for piece in data.chunks(64 * 1024) {
                trust_hmac::Mac::update(&mut ours, piece);
            }
            compare(
                "HMAC-SHA256 (64 KiB pieces vs incumbent single update)",
                &format!("key({key_length}), large_message(seed=7, {length}) in 65536-byte pieces"),
                &k,
                &data,
                ours.finalize().into_bytes().as_ref(),
                &theirs_256(&k, &data),
            );
        }
        println!(
            "multi_megabyte_streamed: {length} bytes in 64 KiB pieces agree under 3 key classes"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. update() split at every offset, under each key class
// ---------------------------------------------------------------------------

const SPLIT_LENGTHS: &[usize] = &[
    0, 1, 2, 3, 31, 32, 54, 55, 56, 63, 64, 65, 110, 111, 112, 119, 120, 127, 128, 129, 191, 192,
    255, 256, 257, 512, 600,
];

/// Every single split point of every length in `SPLIT_LENGTHS`, under a key
/// shorter than B, a key exactly B, and a key longer than B.
///
/// Compared against the incumbent's **single-update** tag, not its split tag:
/// the point is that our streaming path lands on the same value the incumbent's
/// one-shot path does, which is what a cache entry written before the swap and
/// read after it requires.
#[test]
fn every_split_offset_agrees_sha256() {
    let mut splits = 0usize;
    for &(class, key_length) in
        &[("shorter than B", 32usize), ("EXACTLY B", 64), ("longer than B", 100)]
    {
        let k = key(key_length);
        for &length in SPLIT_LENGTHS {
            let data = message(length);
            let reference = theirs_256(&k, &data);
            for split in 0..=length {
                let mut ours = OursSha256::new_from_slice(&k).expect("any key length");
                trust_hmac::Mac::update(&mut ours, &data[..split]);
                trust_hmac::Mac::update(&mut ours, &data[split..]);
                compare(
                    "HMAC-SHA256 two-part vs incumbent single update",
                    &format!(
                        "key class '{class}' key({key_length}), message({length}), split at {split}"
                    ),
                    &k,
                    &data,
                    ours.finalize().into_bytes().as_ref(),
                    &reference,
                );
                splits += 1;
            }
        }
    }
    println!("every_split_offset_sha256: {splits} split points across 3 key classes, all agree");
}

/// The SHA-512 half.
#[test]
fn every_split_offset_agrees_sha512() {
    let mut splits = 0usize;
    for &(class, key_length) in
        &[("shorter than B", 64usize), ("EXACTLY B", 128), ("longer than B", 200)]
    {
        let k = key(key_length);
        for &length in SPLIT_LENGTHS {
            let data = message(length);
            let reference = theirs_512(&k, &data);
            for split in 0..=length {
                let mut ours = OursSha512::new_from_slice(&k).expect("any key length");
                trust_hmac::Mac::update(&mut ours, &data[..split]);
                trust_hmac::Mac::update(&mut ours, &data[split..]);
                compare(
                    "HMAC-SHA512 two-part vs incumbent single update",
                    &format!(
                        "key class '{class}' key({key_length}), message({length}), split at {split}"
                    ),
                    &k,
                    &data,
                    ours.finalize().into_bytes().as_ref(),
                    &reference,
                );
                splits += 1;
            }
        }
    }
    println!("every_split_offset_sha512: {splits} split points across 3 key classes, all agree");
}

/// Maximum fragmentation: one `update` per byte, plus interleaved empty
/// updates, under each key class.
#[test]
fn byte_at_a_time_agrees() {
    for &key_length in &[0usize, 32, 64, 65, 100, 200] {
        let k = key(key_length);
        for &length in &[0usize, 1, 63, 64, 65, 128, 200, 1000] {
            let data = message(length);
            let reference = theirs_256(&k, &data);

            let mut ours = OursSha256::new_from_slice(&k).expect("any key length");
            for byte in &data {
                trust_hmac::Mac::update(&mut ours, &[*byte]);
            }
            compare(
                "HMAC-SHA256 byte-at-a-time",
                &format!("key({key_length}), message({length}), one update per byte"),
                &k,
                &data,
                ours.finalize().into_bytes().as_ref(),
                &reference,
            );

            let mut ours = OursSha256::new_from_slice(&k).expect("any key length");
            trust_hmac::Mac::update(&mut ours, b"");
            for byte in &data {
                trust_hmac::Mac::update(&mut ours, &[*byte]);
                trust_hmac::Mac::update(&mut ours, b"");
            }
            compare(
                "HMAC-SHA256 byte-at-a-time with interleaved empty updates",
                &format!("key({key_length}), message({length})"),
                &k,
                &data,
                ours.finalize().into_bytes().as_ref(),
                &reference,
            );
        }
    }
    println!("byte_at_a_time: 6 key lengths x 8 message lengths x 2 feeds agree");
}

/// Every fixed chunk size 1..=140 over messages that are not a multiple of any
/// of them, under a key in each class. 140 > B for both hashes, so a chunk can
/// straddle two internal blocks.
#[test]
fn every_fixed_chunk_size_agrees() {
    let mut cases = 0usize;
    for &key_length in &[32usize, 64, 100] {
        let k = key(key_length);
        for &length in &[0usize, 199, 517] {
            let data = message(length);
            let reference = theirs_256(&k, &data);
            for chunk in 1..=140usize {
                let mut ours = OursSha256::new_from_slice(&k).expect("any key length");
                for piece in data.chunks(chunk) {
                    trust_hmac::Mac::update(&mut ours, piece);
                }
                compare(
                    "HMAC-SHA256 fixed-chunk feed",
                    &format!("key({key_length}), message({length}), chunk size {chunk}"),
                    &k,
                    &data,
                    ours.finalize().into_bytes().as_ref(),
                    &reference,
                );
                cases += 1;
            }
        }
    }
    println!("every_fixed_chunk_size: {cases} chunked feeds agree");
}
