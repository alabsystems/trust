// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Exhaustive differential against the incumbent `sha2` crate.**
//!
//! Companion to `differential_sha2.rs`, which samples randomly. This file is
//! the *exhaustive* half, targeted at the three input classes where a hash
//! implementation actually goes wrong and where a sampled test can miss:
//!
//! 1. **Every length 0..=200 of deterministic byte patterns.** Deterministic,
//!    not random: a random-content failure is reproducible only if the RNG is,
//!    and a fixed pattern also lets a *reader* regenerate the failing input by
//!    hand. Six patterns, because content matters as well as length — an
//!    all-zero message keeps `Ch`/`Maj` in a degenerate corner, `0xff` keeps
//!    every carry set, `0x80` exercises the top bit of every word.
//! 2. **Multi-megabyte inputs.** The 64-bit length field (FIPS 180-4 §5.1.1)
//!    and the block counter only get interesting past a few thousand blocks.
//!    Sizes are chosen off round numbers so the final partial block is never
//!    the same size twice.
//! 3. **`update` split at EVERY offset.** A single one-shot digest compared
//!    against a two-part feed at every possible split point, plus
//!    byte-at-a-time and every fixed chunk size. This is the class of bug —
//!    an off-by-one in the internal buffer's fill/spill logic — that a
//!    one-shot known-answer test structurally cannot see, and that every
//!    streaming caller in this tree would hit.
//!
//! A failure prints the pattern name, the length, the input bytes (head and
//! tail for large inputs) and BOTH digests, because a disagreement here is the
//! single most valuable thing this crate's test suite can produce.
//!
//! Deleted, with the `sha2` dev-dependency, on the day the incumbent leaves
//! the graph.

use sha2::Digest as _;
use trust_sha2::Digest as _;

// ---------------------------------------------------------------------------
// Deterministic input patterns
// ---------------------------------------------------------------------------

/// The deterministic byte patterns. `(name, generator)`; `generator(i)` is
/// byte `i`, so any prefix of a pattern is that pattern at a shorter length
/// and a failing input can be regenerated from the name and the length alone.
const PATTERNS: &[(&str, fn(usize) -> u8)] = &[
    ("counter", |i| i as u8),
    ("lcg", |i| (i.wrapping_mul(167).wrapping_add(13)) as u8),
    ("zeros", |_| 0x00),
    ("ones", |_| 0xff),
    ("high-bit", |_| 0x80),
    ("ascii", |i| b'a' + (i % 26) as u8),
];

fn pattern(generator: fn(usize) -> u8, length: usize) -> Vec<u8> {
    (0..length).map(generator).collect()
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(&mut out, "{byte:02x}").expect("String write cannot fail");
    }
    out
}

/// Render the input for a failure report: whole thing when small, head and
/// tail when large. The caller also supplies a regeneration recipe.
fn describe_input(data: &[u8]) -> String {
    if data.len() <= 96 {
        format!("{} bytes: {}", data.len(), hex(data))
    } else {
        format!(
            "{} bytes: {}...{} (first 48 and last 48)",
            data.len(),
            hex(&data[..48]),
            hex(&data[data.len() - 48..])
        )
    }
}

/// The one place a disagreement is reported. Prints the recipe, the input and
/// both digests before panicking.
#[track_caller]
fn compare(algorithm: &str, recipe: &str, data: &[u8], ours: &[u8], theirs: &[u8]) {
    if ours != theirs {
        panic!(
            "\n\
             ================ DIFFERENTIAL DISAGREEMENT ================\n\
             algorithm : {algorithm}\n\
             recipe    : {recipe}\n\
             input     : {}\n\
             trust-sha2: {}\n\
             sha2 (inc): {}\n\
             ===========================================================\n",
            describe_input(data),
            hex(ours),
            hex(theirs),
        );
    }
}

/// One-shot agreement across all four widths.
fn one_shot_all_widths(recipe: &str, data: &[u8]) {
    compare(
        "SHA-256",
        recipe,
        data,
        trust_sha2::Sha256::digest(data).as_ref(),
        sha2::Sha256::digest(data).as_slice(),
    );
    compare(
        "SHA-512",
        recipe,
        data,
        trust_sha2::Sha512::digest(data).as_ref(),
        sha2::Sha512::digest(data).as_slice(),
    );
    compare(
        "SHA-224",
        recipe,
        data,
        trust_sha2::Sha224::digest(data).as_ref(),
        sha2::Sha224::digest(data).as_slice(),
    );
    compare(
        "SHA-384",
        recipe,
        data,
        trust_sha2::Sha384::digest(data).as_ref(),
        sha2::Sha384::digest(data).as_slice(),
    );
}

// ---------------------------------------------------------------------------
// 1. Every length 0..=200 of a deterministic byte pattern
// ---------------------------------------------------------------------------

/// Every length from 0 to 200 inclusive, for six deterministic patterns, for
/// all four digest widths.
///
/// 200 bytes spans three SHA-256 blocks and one and a half SHA-512 blocks, so
/// every padding class of both families appears several times: the
/// no-room-for-the-length case (SHA-256 at 56..=63 and 120..=127, SHA-512 at
/// 112..=127), the exact-fit case (55, 119; 111), and the whole-block case
/// (0, 64, 128; 0, 128).
#[test]
fn every_length_to_200_of_deterministic_patterns_agrees() {
    let mut comparisons = 0usize;
    for (name, generator) in PATTERNS {
        for length in 0..=200usize {
            let data = pattern(*generator, length);
            one_shot_all_widths(&format!("pattern {name}, length {length}"), &data);
            comparisons += 4;
        }
    }
    println!(
        "every_length_to_200: {comparisons} digest comparisons \
         ({} patterns x 201 lengths x 4 widths) — all agree",
        PATTERNS.len()
    );
}

// ---------------------------------------------------------------------------
// 2. Multi-megabyte inputs
// ---------------------------------------------------------------------------

/// A multi-megabyte deterministic buffer. Built without an RNG so the recipe
/// in a failure report is exact: `byte[i] = (i*167+13) mod 256`, offset by
/// `seed` so the several sizes do not share a prefix.
fn large_buffer(seed: usize, length: usize) -> Vec<u8> {
    (0..length).map(|i| (i.wrapping_add(seed).wrapping_mul(167).wrapping_add(13)) as u8).collect()
}

/// Several multi-megabyte inputs, one-shot, across the four widths.
///
/// The sizes are deliberately not round: each leaves a different partial final
/// block, and each exercises a different value in the 64-bit (SHA-256) and
/// 128-bit (SHA-512) length field of §5.1. 5,000,007 bytes is 78,125 SHA-256
/// blocks plus a 7-byte tail — past any plausible internal counter width.
#[test]
fn multi_megabyte_inputs_agree() {
    // All four widths on the two smaller sizes.
    for (index, &length) in [1_048_576usize, 2_097_153].iter().enumerate() {
        let data = large_buffer(index * 7, length);
        one_shot_all_widths(&format!("large_buffer(seed={}, length={length})", index * 7), &data);
        println!("multi_megabyte: {length} bytes agree on all four widths");
    }

    // The two largest only on the widths the tree uses, to keep the
    // opt-level-0 test binary honest about its runtime.
    for (index, &length) in [4_194_367usize, 5_000_007].iter().enumerate() {
        let seed = 100 + index * 13;
        let data = large_buffer(seed, length);
        let recipe = format!("large_buffer(seed={seed}, length={length})");
        compare(
            "SHA-256",
            &recipe,
            &data,
            trust_sha2::Sha256::digest(&data).as_ref(),
            sha2::Sha256::digest(&data).as_slice(),
        );
        compare(
            "SHA-512",
            &recipe,
            &data,
            trust_sha2::Sha512::digest(&data).as_ref(),
            sha2::Sha512::digest(&data).as_slice(),
        );
        println!("multi_megabyte: {length} bytes agree on SHA-256 and SHA-512");
    }
}

/// A multi-megabyte input fed through `update` in 64 KiB pieces — the exact
/// shape `trust_buildcache` uses when it streams a file — compared against the
/// incumbent's one-shot digest of the same bytes.
///
/// One-shot-vs-streamed is the comparison that matters: it catches a buffer
/// bug that both implementations' streaming paths could otherwise share.
#[test]
fn multi_megabyte_streamed_in_64k_pieces_agrees() {
    for &length in &[1_048_576usize, 3_000_001, 5_000_007] {
        let data = large_buffer(31, length);

        let mut ours = trust_sha2::Sha256::new();
        for piece in data.chunks(64 * 1024) {
            ours.update(piece);
        }
        compare(
            "SHA-256 (64 KiB pieces vs incumbent one-shot)",
            &format!("large_buffer(seed=31, length={length}) in 65536-byte pieces"),
            &data,
            ours.finalize().as_ref(),
            sha2::Sha256::digest(&data).as_slice(),
        );

        let mut ours = trust_sha2::Sha512::new();
        for piece in data.chunks(64 * 1024) {
            ours.update(piece);
        }
        compare(
            "SHA-512 (64 KiB pieces vs incumbent one-shot)",
            &format!("large_buffer(seed=31, length={length}) in 65536-byte pieces"),
            &data,
            ours.finalize().as_ref(),
            sha2::Sha512::digest(&data).as_slice(),
        );

        println!("multi_megabyte_streamed: {length} bytes in 64 KiB pieces agree");
    }
}

// ---------------------------------------------------------------------------
// 3. update() split at EVERY offset
// ---------------------------------------------------------------------------

/// The lengths for the exhaustive-split sweeps: every small length, both sides
/// of every SHA-256 block boundary (64) and SHA-512 block boundary (128), the
/// padding-edge lengths (55/56, 111/112, 119/120), and one long length that
/// spans many blocks.
const SPLIT_LENGTHS: &[usize] = &[
    0, 1, 2, 3, 4, 5, 6, 7, 8, 31, 32, 54, 55, 56, 57, 63, 64, 65, 110, 111, 112, 113, 118, 119,
    120, 121, 126, 127, 128, 129, 191, 192, 193, 255, 256, 257, 447, 448, 449, 511, 512, 513, 1000,
];

/// **Every single split point of every length in `SPLIT_LENGTHS`.**
///
/// Three things are asserted at each split, and they fail for different
/// reasons:
///
/// * our two-part feed == our one-shot (the digest may not depend on chunking);
/// * our two-part feed == the incumbent's two-part feed (same split);
/// * our two-part feed == the incumbent's one-shot.
///
/// The third is the load-bearing one — the first two could both hold while
/// both implementations agree on a *wrong* answer only in the streamed case.
#[test]
fn every_split_offset_agrees_sha256() {
    let mut splits_checked = 0usize;
    for &length in SPLIT_LENGTHS {
        let data = pattern(|i| (i.wrapping_mul(167).wrapping_add(13)) as u8, length);
        let ours_one_shot = trust_sha2::Sha256::digest(&data);
        let theirs_one_shot = sha2::Sha256::digest(&data);
        compare(
            "SHA-256 one-shot",
            &format!("pattern lcg, length {length}"),
            &data,
            ours_one_shot.as_ref(),
            theirs_one_shot.as_slice(),
        );

        for split in 0..=length {
            let mut ours = trust_sha2::Sha256::new();
            ours.update(&data[..split]);
            ours.update(&data[split..]);
            let ours = ours.finalize();

            let mut theirs = sha2::Sha256::new();
            theirs.update(&data[..split]);
            theirs.update(&data[split..]);
            let theirs = theirs.finalize();

            let recipe = format!("pattern lcg, length {length}, split at {split}");
            compare(
                "SHA-256 two-part vs incumbent two-part",
                &recipe,
                &data,
                ours.as_ref(),
                &theirs,
            );
            compare(
                "SHA-256 two-part vs incumbent one-shot",
                &recipe,
                &data,
                ours.as_ref(),
                theirs_one_shot.as_slice(),
            );
            compare(
                "SHA-256 two-part vs OUR one-shot",
                &recipe,
                &data,
                ours.as_ref(),
                ours_one_shot.as_ref(),
            );
            splits_checked += 1;
        }
    }
    println!("every_split_offset_sha256: {splits_checked} split points, all agree");
}

/// The SHA-512 half of `every_split_offset_agrees_sha256`. Separate test so a
/// failure names the family without reading the message.
#[test]
fn every_split_offset_agrees_sha512() {
    let mut splits_checked = 0usize;
    for &length in SPLIT_LENGTHS {
        let data = pattern(|i| (i.wrapping_mul(167).wrapping_add(13)) as u8, length);
        let ours_one_shot = trust_sha2::Sha512::digest(&data);
        let theirs_one_shot = sha2::Sha512::digest(&data);
        compare(
            "SHA-512 one-shot",
            &format!("pattern lcg, length {length}"),
            &data,
            ours_one_shot.as_ref(),
            theirs_one_shot.as_slice(),
        );

        for split in 0..=length {
            let mut ours = trust_sha2::Sha512::new();
            ours.update(&data[..split]);
            ours.update(&data[split..]);
            let ours = ours.finalize();

            let mut theirs = sha2::Sha512::new();
            theirs.update(&data[..split]);
            theirs.update(&data[split..]);
            let theirs = theirs.finalize();

            let recipe = format!("pattern lcg, length {length}, split at {split}");
            compare(
                "SHA-512 two-part vs incumbent two-part",
                &recipe,
                &data,
                ours.as_ref(),
                &theirs,
            );
            compare(
                "SHA-512 two-part vs incumbent one-shot",
                &recipe,
                &data,
                ours.as_ref(),
                theirs_one_shot.as_slice(),
            );
            compare(
                "SHA-512 two-part vs OUR one-shot",
                &recipe,
                &data,
                ours.as_ref(),
                ours_one_shot.as_ref(),
            );
            splits_checked += 1;
        }
    }
    println!("every_split_offset_sha512: {splits_checked} split points, all agree");
}

/// Maximum fragmentation: one `update` per byte, against the incumbent's
/// one-shot. Also the zero-length-update case interleaved, which is the
/// degenerate input a `Write` adapter can produce.
#[test]
fn byte_at_a_time_agrees() {
    for &length in &[0usize, 1, 2, 63, 64, 65, 127, 128, 129, 200, 1000, 4096] {
        let data = pattern(|i| i as u8, length);

        let mut ours = trust_sha2::Sha256::new();
        for byte in &data {
            ours.update([*byte]);
        }
        compare(
            "SHA-256 byte-at-a-time",
            &format!("pattern counter, length {length}, one update per byte"),
            &data,
            ours.finalize().as_ref(),
            sha2::Sha256::digest(&data).as_slice(),
        );

        let mut ours = trust_sha2::Sha512::new();
        for byte in &data {
            ours.update([*byte]);
        }
        compare(
            "SHA-512 byte-at-a-time",
            &format!("pattern counter, length {length}, one update per byte"),
            &data,
            ours.finalize().as_ref(),
            sha2::Sha512::digest(&data).as_slice(),
        );

        // Empty updates interleaved between every byte.
        let mut ours = trust_sha2::Sha256::new();
        ours.update(b"");
        for byte in &data {
            ours.update([*byte]);
            ours.update(b"");
        }
        compare(
            "SHA-256 byte-at-a-time with interleaved empty updates",
            &format!("pattern counter, length {length}"),
            &data,
            ours.finalize().as_ref(),
            sha2::Sha256::digest(&data).as_slice(),
        );
    }
    println!("byte_at_a_time: 12 lengths x 3 feeds, all agree");
}

/// Every fixed chunk size from 1 to 200 over messages that are not a multiple
/// of any of them. Catches a spill bug that only fires when a chunk straddles
/// the internal buffer boundary by a specific amount.
#[test]
fn every_fixed_chunk_size_agrees() {
    let mut cases = 0usize;
    for &length in &[0usize, 199, 256, 517, 1024] {
        let data = pattern(|i| (i.wrapping_mul(167).wrapping_add(13)) as u8, length);
        let theirs_256 = sha2::Sha256::digest(&data);
        let theirs_512 = sha2::Sha512::digest(&data);

        for chunk in 1..=200usize {
            let mut ours = trust_sha2::Sha256::new();
            for piece in data.chunks(chunk) {
                ours.update(piece);
            }
            compare(
                "SHA-256 fixed-chunk feed",
                &format!("pattern lcg, length {length}, chunk size {chunk}"),
                &data,
                ours.finalize().as_ref(),
                theirs_256.as_slice(),
            );

            let mut ours = trust_sha2::Sha512::new();
            for piece in data.chunks(chunk) {
                ours.update(piece);
            }
            compare(
                "SHA-512 fixed-chunk feed",
                &format!("pattern lcg, length {length}, chunk size {chunk}"),
                &data,
                ours.finalize().as_ref(),
                theirs_512.as_slice(),
            );
            cases += 2;
        }
    }
    println!("every_fixed_chunk_size: {cases} chunked feeds, all agree");
}
