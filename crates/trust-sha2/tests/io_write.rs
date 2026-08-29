// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! `std::io::Write` for the hashers — the `io::copy` sink shape.
//!
//! This exists because six `targo-trust` sites and one in `build-manifest`
//! stream a file into a digest with `io::copy(&mut reader, &mut hasher)` rather
//! than reading it into memory. The incumbent supports that through `digest`'s
//! `std` feature; without the impl those sites fail with
//! `error[E0277]: the trait bound `Sha256: std::io::Write` is not satisfied`.
//!
//! The load-bearing property is not that `Write` *exists* but that writing
//! through it produces the SAME digest as `update` — an impl that silently
//! dropped or reordered bytes would still compile and still return a hash.
//! Every test below therefore compares against a known-good digest computed
//! the ordinary way, and one compares against the incumbent directly.

#![cfg(feature = "std")]

use std::io::Write;

use trust_sha2::{Digest, Sha224, Sha256, Sha384, Sha512};

/// `io::copy` from a reader must equal a single `update` of the same bytes.
///
/// `io::copy` chooses its own buffer size, so this also exercises the
/// arbitrary-chunk-boundary path through `write`.
#[test]
fn io_copy_equals_update() {
    // Large enough that io::copy issues many writes at its internal buffer
    // size, and not a multiple of any block size (64 / 128).
    let data: Vec<u8> = (0..70_001u32).map(|i| (i % 251) as u8).collect();

    let mut direct = Sha256::new();
    direct.update(&data);
    let expected = direct.finalize();

    let mut sink = Sha256::new();
    let copied = std::io::copy(&mut data.as_slice(), &mut sink).expect("copy");
    assert_eq!(copied, data.len() as u64);
    assert_eq!(sink.finalize(), expected);
}

/// The same for all four widths, including the empty input.
#[test]
fn io_copy_all_widths_and_empty() {
    macro_rules! check {
        ($h:ty, $bytes:expr) => {{
            let data: &[u8] = $bytes;

            let mut direct = <$h>::new();
            direct.update(data);
            let expected = direct.finalize();

            let mut sink = <$h>::new();
            std::io::copy(&mut { data }, &mut sink).expect("copy");
            assert_eq!(
                sink.finalize(),
                expected,
                "io::copy disagreed for {} on {} bytes",
                stringify!($h),
                data.len()
            );
        }};
    }

    for bytes in [b"".as_slice(), b"abc".as_slice(), &[0xa5u8; 1000]] {
        check!(Sha224, bytes);
        check!(Sha256, bytes);
        check!(Sha384, bytes);
        check!(Sha512, bytes);
    }
}

/// `write` must consume the entire buffer every time.
///
/// If it ever returned a short count, `write_all` would loop and re-feed the
/// tail — producing a wrong digest rather than an error. Pinned explicitly
/// because the bug is silent.
#[test]
fn write_consumes_whole_buffer() {
    let mut hasher = Sha256::new();
    for len in [0usize, 1, 55, 56, 63, 64, 65, 127, 128, 129, 1000] {
        let buf = vec![0x5au8; len];
        assert_eq!(hasher.write(&buf).expect("write"), len, "short write at len {len}");
    }
    assert!(hasher.flush().is_ok());
}

/// Interleaving `write` and `update` must be indistinguishable from one
/// contiguous message — they are the same absorb path.
#[test]
fn write_and_update_interleave() {
    let mut mixed = Sha512::new();
    mixed.write_all(b"the quick ").unwrap();
    mixed.update("brown fox ");
    mixed.write_all(b"jumps over ").unwrap();
    mixed.update(b"the lazy dog");

    let mut direct = Sha512::new();
    direct.update("the quick brown fox jumps over the lazy dog");

    assert_eq!(mixed.finalize(), direct.finalize());
}

/// The acceptance gate: the `Write` path must agree with the INCUMBENT, not
/// merely with our own `update`. Both self-consistency tests above would still
/// pass if `update` itself were wrong.
#[test]
fn io_copy_matches_incumbent() {
    use sha2::Digest as _;

    for len in [0usize, 1, 55, 56, 63, 64, 65, 127, 128, 129, 4096, 70_001] {
        let data: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();

        let mut ours = Sha256::new();
        std::io::copy(&mut data.as_slice(), &mut ours).expect("copy");

        let mut theirs = sha2::Sha256::new();
        std::io::copy(&mut data.as_slice(), &mut theirs).expect("copy");

        assert_eq!(
            ours.finalize().as_ref(),
            theirs.finalize().as_slice(),
            "io::copy digest disagreed with the incumbent at len {len}"
        );
    }
}
