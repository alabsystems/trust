// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Known-answer tests from FIPS PUB 180-4 and the standard published vectors.
//!
//! Provenance of every expected value in this file:
//!
//! * FIPS PUB 180-4, Appendix A (SHA-256 examples), Appendix B (SHA-224/384/512
//!   examples) and Appendix C — the one-block message `"abc"`, the two-block
//!   messages, and the 1,000,000-`'a'` message.
//! * The empty message, which the appendices do not carry but which every
//!   implementation must agree on and which exercises the "padding is the whole
//!   message" path.
//!
//! Each was re-checked against CPython's `hashlib` (OpenSSL) before being
//! written down, so a mis-transcribed *vector* fails here at authoring time
//! rather than being mistaken for a mis-implemented *hash* later.

use trust_sha2::{Digest, NativeSha256, Sha224, Sha256, Sha384, Sha512};

/// FIPS 180-4 Appendix A/B two-block message: 56 bytes.
///
/// Note this is exactly the SHA-256 padding edge: 56 + 1 pad byte = 57 > 56, so
/// the length field does not fit and a second compression is required.
const TWO_BLOCK_448: &[u8] = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";

/// FIPS 180-4 Appendix B/C two-block message for the 512-bit family: 112 bytes.
///
/// The SHA-512 padding edge, for the same reason: 112 + 1 > 112.
const TWO_BLOCK_896: &[u8] = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";

fn hex<D: Digest>(data: &[u8]) -> String {
    let digest = D::digest(data);
    let mut out = String::with_capacity(digest.as_ref().len() * 2);
    for byte in digest.as_ref() {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("String write cannot fail");
    }
    out
}

#[test]
fn sha256_empty() {
    assert_eq!(
        hex::<Sha256>(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
}

#[test]
fn sha256_abc_one_block() {
    // FIPS 180-4 Appendix A.1.
    assert_eq!(
        hex::<Sha256>(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
}

#[test]
fn sha256_two_block() {
    // FIPS 180-4 Appendix A.2.
    assert_eq!(
        hex::<Sha256>(TWO_BLOCK_448),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
}

#[test]
fn sha256_multi_block() {
    // The 896-bit message: three SHA-256 blocks after padding.
    assert_eq!(
        hex::<Sha256>(TWO_BLOCK_896),
        "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
    );
}

#[test]
fn sha256_million_a() {
    // FIPS 180-4 Appendix A.3: 1,000,000 repetitions of 'a'. 15,625 blocks —
    // the only vector here that exercises the state machine at scale.
    let message = vec![b'a'; 1_000_000];
    assert_eq!(
        hex::<Sha256>(&message),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
}

#[test]
fn native_sha256_published_vectors_cover_padding_and_streaming() {
    for (input, expected) in [
        (&b""[..], "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        (&b"abc"[..], "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
        (TWO_BLOCK_448, "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
        (TWO_BLOCK_896, "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
    ] {
        assert_eq!(hex::<NativeSha256>(input), expected);
    }
    let mut hasher = NativeSha256::new();
    for _ in 0..1000 {
        hasher.update([b'a'; 1000]);
    }
    assert_eq!(
        format!("{:x}", hasher.finalize()),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
}

#[test]
fn sha256_hello_world() {
    assert_eq!(
        hex::<Sha256>(b"hello world"),
        "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
    );
}

#[test]
fn sha512_empty() {
    assert_eq!(
        hex::<Sha512>(b""),
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce\
         47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    );
}

#[test]
fn sha512_abc_one_block() {
    // FIPS 180-4 Appendix C.1.
    assert_eq!(
        hex::<Sha512>(b"abc"),
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
         2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    );
}

#[test]
fn sha512_short_message_single_block() {
    // 56 bytes: one SHA-512 block, well inside the 112-byte length edge.
    assert_eq!(
        hex::<Sha512>(TWO_BLOCK_448),
        "204a8fc6dda82f0a0ced7beb8e08a41657c16ef468b228a8279be331a703c335\
         96fd15c13b1b07f9aa1d3bea57789ca031ad85c7a71dd70354ec631238ca3445"
    );
}

#[test]
fn sha512_two_block() {
    // FIPS 180-4 Appendix C.2.
    assert_eq!(
        hex::<Sha512>(TWO_BLOCK_896),
        "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018\
         501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
    );
}

#[test]
fn sha512_million_a() {
    // FIPS 180-4 Appendix C.3.
    let message = vec![b'a'; 1_000_000];
    assert_eq!(
        hex::<Sha512>(&message),
        "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973eb\
         de0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b"
    );
}

#[test]
fn sha224_vectors() {
    assert_eq!(hex::<Sha224>(b""), "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f");
    // FIPS 180-4 Appendix B.1 / B.2.
    assert_eq!(hex::<Sha224>(b"abc"), "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7");
    assert_eq!(
        hex::<Sha224>(TWO_BLOCK_448),
        "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525"
    );
}

#[test]
fn sha384_vectors() {
    assert_eq!(
        hex::<Sha384>(b""),
        "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da\
         274edebfe76f65fbd51ad2f14898b95b"
    );
    // FIPS 180-4 Appendix D.1 / D.2.
    assert_eq!(
        hex::<Sha384>(b"abc"),
        "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed\
         8086072ba1e7cc2358baeca134c825a7"
    );
    assert_eq!(
        hex::<Sha384>(TWO_BLOCK_896),
        "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712\
         fcc7c71a557e2db966c3e9fa91746039"
    );
}

/// The `LowerHex` impl is the form 174 call sites actually use; it must agree
/// with a hand-rolled `{:02x}` loop over the same bytes.
#[test]
fn lower_hex_matches_manual_rendering() {
    for length in [0usize, 1, 55, 56, 64, 200] {
        let message: Vec<u8> = (0..length).map(|i| (i as u8).wrapping_mul(31)).collect();
        let digest = Sha256::digest(&message);
        assert_eq!(format!("{digest:x}"), hex::<Sha256>(&message));
        assert_eq!(format!("{digest:x}").len(), 64);
        assert!(
            format!("{digest:x}").chars().all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c))
        );
    }
}
