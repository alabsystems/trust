// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Liveness and plumbing tests for the public surface of `trust-rand`.
//!
//! # READ THIS BEFORE TREATING A GREEN RUN AS EVIDENCE OF ANYTHING
//!
//! **These tests establish that the plumbing is live. They do not establish
//! that the output is random, and no test in this file or any other could.**
//!
//! The reason is not that the tests here are weak; it is structural. Every
//! finite output of a perfect CSPRNG is also a possible output of a
//! catastrophically broken one, and vice versa. A statistical test that passes
//! is consistent with a compromised source; a statistical test that fails is
//! consistent with a working source. Adding chi-squared or monobit assertions
//! would add flakiness and the *appearance* of cryptographic evidence without
//! adding any, which is worse than not having them — so they are deliberately
//! absent.
//!
//! What these tests do catch is the realistic failure: a source that is dead,
//! stubbed, short, or writing the wrong number of bytes. That is a plumbing
//! question, it is decidable, and it is what is asserted below. The quality
//! question is answered by the operating system's CSPRNG, cited per platform in
//! the `os` and `urandom` module documentation.
//!
//! Where an assertion is probabilistic rather than certain, the exact false-
//! failure probability is stated at the assertion.

use trust_rand::{fill_bytes, secret_seed_32, try_fill_bytes, try_secret_seed_32};

/// The sentinel a destination buffer is pre-filled with. Chosen non-zero so
/// that "never written" is distinguishable from "written with zeros", and
/// non-`0xFF` so that a memset-to-all-ones defect is also visible.
const SENTINEL: u8 = 0xA5;

/// A dead or stubbed source is the realistic plumbing failure, and it produces
/// a buffer of zeros. False-failure probability for a working source: 2^-2048.
#[test]
fn a_draw_is_not_all_zero() {
    let mut buf = [0u8; 256];
    fill_bytes(&mut buf);
    assert!(buf.iter().any(|&b| b != 0), "a 256-byte draw was entirely zero");
}

/// A source that is read once and cached — or one that returns a constant —
/// passes the all-zero test and fails this one.
/// False-failure probability: 2^-256.
#[test]
fn two_successive_draws_differ() {
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    fill_bytes(&mut a);
    fill_bytes(&mut b);
    assert_ne!(a, b, "two successive 32-byte draws were identical");
}

/// Stronger than the pair above: a counter-based or slowly-advancing source
/// (the failure mode of `RandomState`, which increments a per-thread key) would
/// pass `two_successive_draws_differ` and could still collide here.
/// With 64 draws of 32 bytes, false-failure probability is under 2^-245.
#[test]
fn many_successive_draws_are_pairwise_distinct() {
    let mut draws = Vec::new();
    for _ in 0..64 {
        let mut buf = [0u8; 32];
        fill_bytes(&mut buf);
        draws.push(buf);
    }
    for i in 0..draws.len() {
        for j in (i + 1)..draws.len() {
            assert_ne!(draws[i], draws[j], "draws {i} and {j} were identical");
        }
    }
}

/// Exactly the requested bytes are written and **nothing outside them is
/// touched**, across every length that interacts with the 256-byte chunk
/// boundary of the primary arm.
///
/// The guard assertion is the strict half: 64 sentinel bytes on each side must
/// survive byte-identically. A source that overruns by even one byte has a
/// 255/256 chance of being caught per byte, so the probability of an
/// undetected overrun of `n` bytes is 256^-n.
///
/// The fill assertion is the probabilistic half: the requested region must
/// contain at least one non-sentinel byte, which for a working source fails
/// with probability 256^-len.
#[test]
fn exactly_the_requested_length_is_written() {
    const GUARD: usize = 64;

    for len in [0usize, 1, 2, 31, 32, 33, 63, 64, 127, 255, 256, 257, 511, 512, 4096] {
        let mut backing = vec![SENTINEL; GUARD + len + GUARD];
        fill_bytes(&mut backing[GUARD..GUARD + len]);

        assert!(
            backing[..GUARD].iter().all(|&b| b == SENTINEL),
            "len={len}: bytes were written BEFORE the start of the destination"
        );
        assert!(
            backing[GUARD + len..].iter().all(|&b| b == SENTINEL),
            "len={len}: bytes were written PAST the end of the destination"
        );

        if len >= 8 {
            assert!(
                backing[GUARD..GUARD + len].iter().any(|&b| b != SENTINEL),
                "len={len}: the destination was left at its sentinel — nothing was written"
            );
        }
    }
}

/// The tail specifically. A chunk loop that drops its final partial chunk fills
/// the first 4096 bytes of a 4096+37 request and leaves 37 at the sentinel;
/// `exactly_the_requested_length_is_written` would still pass on the
/// any-non-sentinel check, so the tail gets its own assertion.
/// False-failure probability: 256^-37.
#[test]
fn a_large_draw_is_filled_all_the_way_to_the_end() {
    let len = 4096 + 37;
    let mut buf = vec![SENTINEL; len];
    fill_bytes(&mut buf);

    for (i, window) in buf.chunks(256).enumerate() {
        assert!(
            window.iter().any(|&b| b != SENTINEL),
            "window {i} (offset {}, {} bytes) was never written",
            i * 256,
            window.len()
        );
    }
    let tail = &buf[4096..];
    assert_eq!(tail.len(), 37);
    assert!(tail.iter().any(|&b| b != SENTINEL), "the trailing partial chunk was never written");
}

/// A draw far larger than any call site needs, to show the chunk loop scales
/// and does not, for instance, quadratically re-request. 1 MiB.
#[test]
fn a_one_mebibyte_draw_succeeds_and_is_written_throughout() {
    let mut buf = vec![SENTINEL; 1 << 20];
    try_fill_bytes(&mut buf).expect("a 1 MiB draw must succeed");
    for (i, window) in buf.chunks(4096).enumerate() {
        assert!(
            window.iter().any(|&b| b != SENTINEL),
            "4 KiB window {i} (offset {}) was never written",
            i * 4096
        );
    }
}

#[test]
fn an_empty_draw_succeeds() {
    try_fill_bytes(&mut []).expect("an empty draw must succeed");
    fill_bytes(&mut []);
}

#[test]
fn a_secret_seed_is_32_bytes_and_is_not_all_zero() {
    let seed = secret_seed_32();
    assert_eq!(seed.len(), 32);
    assert!(seed.iter().any(|&b| b != 0), "the secret seed was entirely zero");
}

/// The property that actually matters for key generation.
/// False-failure probability: 2^-256.
#[test]
fn two_secret_seeds_differ() {
    let a = try_secret_seed_32().expect("a secret seed must be obtainable");
    let b = try_secret_seed_32().expect("a secret seed must be obtainable");
    assert_ne!(a, b, "two successive secret seeds were identical");
}

/// Entropy is drawn per call, not per thread — the `RandomState` failure mode
/// (a key cached once per thread and then incremented) would show up here as
/// structure across threads. This asserts distinctness only, which is all that
/// can be asserted.
#[test]
fn draws_from_different_threads_are_distinct() {
    let handles: Vec<_> = (0..8)
        .map(|_| {
            std::thread::spawn(|| {
                let mut buf = [0u8; 32];
                fill_bytes(&mut buf);
                buf
            })
        })
        .collect();

    let mut draws: Vec<[u8; 32]> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    draws.sort_unstable();
    let before = draws.len();
    draws.dedup();
    assert_eq!(before, draws.len(), "two threads produced identical 32-byte draws");
}
