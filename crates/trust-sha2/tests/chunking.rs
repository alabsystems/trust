// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Chunk-boundary independence.
//!
//! `update` must depend only on the concatenation of everything it has been
//! given, never on how the byte stream was sliced. This is the property that
//! hand-written hashes actually get wrong, and it is the property every
//! streaming caller in this tree relies on:
//!
//! * `trust_types::digest::stable_sha256_hex_reader` feeds an 8 KiB buffer's
//!   worth at a time, with the last read short.
//! * `trust_buildcache::integrity::update_entry_hmac` fed a 64 KiB buffer's
//!   worth at a time, interleaved with 1-byte and 8-byte framing pushes, and
//!   `trust_buildcache::key::hash_bytes` alternated 8-byte lengths with
//!   arbitrary-length values. T11 deleted both; the shapes stay under test.
//!
//! A one-shot KAT cannot see a bug here at all: it makes exactly one `update`
//! call, so the buffering path it exercises is the trivial one.

use trust_sha2::{Digest, Sha224, Sha256, Sha384, Sha512};

fn message(length: usize) -> Vec<u8> {
    (0..length).map(|i| ((i * 31 + 7) & 0xff) as u8).collect()
}

/// Hash `data` by feeding it in chunks of exactly `chunk` bytes (last short).
fn hash_in_chunks<D: Digest>(data: &[u8], chunk: usize) -> Vec<u8> {
    let mut hasher = D::new();
    for piece in data.chunks(chunk.max(1)) {
        hasher.update(piece);
    }
    hasher.finalize().as_ref().to_vec()
}

/// Hash `data` by feeding it at the given split points.
fn hash_at_splits<D: Digest>(data: &[u8], splits: &[usize]) -> Vec<u8> {
    let mut hasher = D::new();
    let mut position = 0;
    for &split in splits {
        let split = split.min(data.len());
        if split > position {
            hasher.update(&data[position..split]);
            position = split;
        }
    }
    hasher.update(&data[position..]);
    hasher.finalize().as_ref().to_vec()
}

/// Every fixed chunk size from 1 to 200 must give the one-shot answer, for a
/// message long enough to span four SHA-512 blocks.
#[test]
fn every_uniform_chunk_size_agrees() {
    let data = message(517);

    let reference_256 = Sha256::digest(&data).as_ref().to_vec();
    let reference_512 = Sha512::digest(&data).as_ref().to_vec();
    let reference_224 = Sha224::digest(&data).as_ref().to_vec();
    let reference_384 = Sha384::digest(&data).as_ref().to_vec();

    for chunk in 1..=200 {
        assert_eq!(
            hash_in_chunks::<Sha256>(&data, chunk),
            reference_256,
            "SHA-256 depends on chunk size {chunk}"
        );
        assert_eq!(
            hash_in_chunks::<Sha512>(&data, chunk),
            reference_512,
            "SHA-512 depends on chunk size {chunk}"
        );
        assert_eq!(
            hash_in_chunks::<Sha224>(&data, chunk),
            reference_224,
            "SHA-224 depends on chunk size {chunk}"
        );
        assert_eq!(
            hash_in_chunks::<Sha384>(&data, chunk),
            reference_384,
            "SHA-384 depends on chunk size {chunk}"
        );
    }
}

/// Every single split point of a three-block message, which is where a
/// "top up the partial block, then take whole blocks" bug shows up.
#[test]
fn every_single_split_agrees() {
    for length in [0usize, 1, 55, 56, 63, 64, 65, 111, 112, 127, 128, 129, 200] {
        let data = message(length);
        let reference_256 = Sha256::digest(&data).as_ref().to_vec();
        let reference_512 = Sha512::digest(&data).as_ref().to_vec();
        for split in 0..=length {
            assert_eq!(
                hash_at_splits::<Sha256>(&data, &[split]),
                reference_256,
                "SHA-256 length {length} split at {split}"
            );
            assert_eq!(
                hash_at_splits::<Sha512>(&data, &[split]),
                reference_512,
                "SHA-512 length {length} split at {split}"
            );
        }
    }
}

/// Every pair of split points of a two-block message: catches the case where
/// the buffer is topped up twice without an intervening compression.
#[test]
fn every_pair_of_splits_agrees() {
    let length = 150;
    let data = message(length);
    let reference_256 = Sha256::digest(&data).as_ref().to_vec();
    let reference_512 = Sha512::digest(&data).as_ref().to_vec();

    for first in 0..=length {
        for second in first..=length {
            assert_eq!(
                hash_at_splits::<Sha256>(&data, &[first, second]),
                reference_256,
                "SHA-256 splits {first}/{second}"
            );
            assert_eq!(
                hash_at_splits::<Sha512>(&data, &[first, second]),
                reference_512,
                "SHA-512 splits {first}/{second}"
            );
        }
    }
}

/// Zero-length `update` calls, anywhere and repeatedly, must be no-ops.
///
/// `trust_buildcache::integrity` (deleted by T11) could issue one: a sealed
/// input of length 0 yielded `mac.update(&buffer[..0])` on the loop's guard
/// path.
#[test]
fn empty_updates_are_no_ops() {
    let data = message(130);
    let reference = Sha256::digest(&data).as_ref().to_vec();

    let mut hasher = Sha256::new();
    hasher.update(b"");
    for byte in &data {
        hasher.update(b"");
        hasher.update(core::slice::from_ref(byte));
        hasher.update(b"");
    }
    hasher.update(b"");
    assert_eq!(hasher.finalize().as_ref().to_vec(), reference);

    // And the fully degenerate case: nothing but empty updates.
    let mut hasher = Sha256::new();
    for _ in 0..1000 {
        hasher.update(b"");
    }
    assert_eq!(hasher.finalize().as_ref().to_vec(), Sha256::digest(b"").as_ref().to_vec());
}

/// A hasher fed exactly one block at a time, for many blocks — the path where
/// `update` compresses out of the caller's slice without buffering at all.
#[test]
fn exact_block_feeds_agree() {
    for blocks in 1..=8 {
        let data_256 = message(blocks * 64);
        assert_eq!(
            hash_in_chunks::<Sha256>(&data_256, 64),
            Sha256::digest(&data_256).as_ref().to_vec(),
            "SHA-256 fed {blocks} whole blocks"
        );

        let data_512 = message(blocks * 128);
        assert_eq!(
            hash_in_chunks::<Sha512>(&data_512, 128),
            Sha512::digest(&data_512).as_ref().to_vec(),
            "SHA-512 fed {blocks} whole blocks"
        );
    }
}
