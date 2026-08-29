// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Does the name `sha2` reach the FIPS 180-4 implementation, and does it carry
//! everything the consumers actually spell?
//!
//! This crate is an alias, so its two failure modes are both silent:
//!
//! * it could re-export something that has the right *shape* but computes a
//!   different digest — every consumer keeps compiling, and thirty-two crates
//!   across seven repositories silently change the identity of every cache
//!   key, certificate name and provenance record they emit;
//! * it could be *incomplete*, in which case the error surfaces inside a
//!   submodule's crate rather than here.
//!
//! `§1` covers the first by pinning published digests through this crate's own
//! name. `§2` covers the second by writing out the call shapes that were
//! measured in the consumers, so that an omission fails to compile in this
//! file.
//!
//! # PROVENANCE OF EXPECTED VALUES — all PUBLISHED, none derived
//!
//! Every expected digest in `§1` is a **published** vector: FIPS PUB 180-4
//! Appendix A (SHA-256), B (SHA-224), C (SHA-512) and D (SHA-384), plus the
//! empty message, which the appendices do not carry but on which every
//! implementation must agree and which exercises the "padding is the whole
//! message" path.
//!
//! **No value here was derived from the incumbent `sha2` crate**, and this
//! file does not depend on it. That is deliberate: this file's job is to prove
//! the alias reaches FIPS-correct code, and a value copied out of the thing
//! being replaced could not distinguish "correct" from "identical to the
//! incumbent". The incumbent differential is a separate, and separately
//! motivated, gate — `crates/trust-sha2/tests/differential_sha2.rs`.
//!
//! These same vectors appear in `crates/trust-sha2/tests/kat.rs`. The
//! duplication is intentional and is not redundancy: that file tests the
//! implementation through the path `trust_sha2::`, this one tests the export
//! path through `sha2::`. A re-export bug is invisible to the former by
//! construction.

// The crate under test is `sha2` — that is the entire point of it.
use sha2::{Digest, Sha224, Sha256, Sha384, Sha512};

/// FIPS 180-4 Appendix A.2 two-block message, 56 bytes: the SHA-256 padding
/// edge, where 56 + 1 pad byte leaves no room for the length field.
const TWO_BLOCK_448: &[u8] = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";

fn hex<D: Digest>(data: &[u8]) -> String {
    use std::fmt::Write as _;
    let digest = D::digest(data);
    let mut out = String::with_capacity(digest.as_ref().len() * 2);
    for byte in digest.as_ref() {
        write!(&mut out, "{byte:02x}").expect("String write cannot fail");
    }
    out
}

// ---------------------------------------------------------------------------
// §1  The alias reaches FIPS 180-4, not a look-alike.
// ---------------------------------------------------------------------------

#[test]
fn sha256_published_vectors_through_the_sha2_name() {
    // Empty message.
    assert_eq!(
        hex::<Sha256>(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    // FIPS 180-4 Appendix A.1.
    assert_eq!(
        hex::<Sha256>(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    // FIPS 180-4 Appendix A.2.
    assert_eq!(
        hex::<Sha256>(TWO_BLOCK_448),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
}

#[test]
fn sha224_384_512_published_vectors_through_the_sha2_name() {
    // FIPS 180-4 Appendix B.1.
    assert_eq!(hex::<Sha224>(b"abc"), "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7");
    // FIPS 180-4 Appendix D.1.
    assert_eq!(
        hex::<Sha384>(b"abc"),
        "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed\
         8086072ba1e7cc2358baeca134c825a7"
    );
    // FIPS 180-4 Appendix C.1.
    assert_eq!(
        hex::<Sha512>(b"abc"),
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
         2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    );
}

// ---------------------------------------------------------------------------
// §2  The alias carries every call shape the consumers spell.
//
// The shapes below were measured, not imagined: `grep` over the seven in-scope
// `first-party/*` repositories found 120 `sha2::` sites in exactly four import
// forms (101 `use sha2::{Digest, Sha256}`, 16 `use sha2::{Digest as _,
// Sha256}`, 2 `use sha2::Digest as _`, 2 fully-qualified `sha2::Sha256::`),
// and the value-level usage in `first-party/ay` adds the five expression
// shapes covered by `ay_measured_expression_shapes`.
//
// These tests assert little; their value is that they must COMPILE.
// ---------------------------------------------------------------------------

#[test]
fn import_form_streaming_hasher() {
    // `use sha2::{Digest, Sha256};` — 101 sites, the dominant form.
    let mut hasher = Sha256::new();
    hasher.update(b"hello ");
    hasher.update("world".as_bytes());
    let digest = hasher.finalize();
    assert_eq!(
        format!("{digest:x}"),
        "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
    );
}

#[test]
fn import_form_fully_qualified() {
    // `sha2::Sha256::digest(..)` with `use sha2::Digest as _;` — 4 sites.
    use sha2::Digest as _;
    assert_eq!(
        format!("{:x}", sha2::Sha256::digest(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
}

#[test]
fn ay_measured_expression_shapes() {
    // Each of these is a real line shape from `first-party/ay`. The comment
    // names the file it was measured in.

    // ay-milp/src/cert_io.rs, ay/src/run.rs: `Sha256` as a struct field, in a
    // struct that is moved and mutated through `&mut self`.
    struct CanonicalDigestWriter {
        digest: Sha256,
    }
    let mut writer = CanonicalDigestWriter { digest: Sha256::new() };
    writer.digest.update(b"abc");

    // ay-test-support/src/lib.rs: `&mut Sha256` passed to a helper.
    fn feed(enumerator: &mut Sha256, bytes: &[u8]) {
        enumerator.update(bytes);
    }
    feed(&mut writer.digest, b"");
    assert_eq!(
        format!("{:x}", writer.digest.finalize()),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );

    // ay/src/run.rs: `format!("{:x}", Sha256::digest(&bytes))` — LowerHex on
    // the output, and `&Vec<u8>` (not `&[u8]`) as the argument.
    let bytes: Vec<u8> = b"abc".to_vec();
    assert_eq!(
        format!("{:x}", Sha256::digest(&bytes)),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );

    // ay-sat: `hex_encode(&Sha256::digest(bytes))` — `&Output` where `&[u8]`
    // is expected, which needs Deref COERCION, not `AsRef`.
    fn hex_encode(raw: &[u8]) -> usize {
        raw.len()
    }
    assert_eq!(hex_encode(&Sha256::digest(b"abc")), 32);

    // ay-quality-gate: `let h: [u8; 32] = Sha256::digest(..).into();`
    let historical: [u8; 32] = Sha256::digest(b"abc").into();
    assert_eq!(historical[0], 0xba);

    // ay/src/cmd_bench_campaign.rs: the hasher is cloned into a struct that
    // derives Clone.
    #[derive(Clone)]
    struct DigestingReader {
        hasher: Sha256,
    }
    let reader = DigestingReader { hasher: Sha256::new() };
    let mut forked = reader.clone();
    forked.hasher.update(b"abc");
    assert_eq!(
        format!("{:x}", forked.hasher.finalize()),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
}

#[test]
fn chunking_does_not_change_the_digest() {
    // The failure a streaming consumer actually hits: `ProofDigestWriter` and
    // `DigestingReader` in ay feed the hasher in `io::copy`-sized pieces, so
    // the digest must not depend on where the boundaries fell.
    let message: Vec<u8> = (0u8..=255).cycle().take(600).collect();
    let one_shot = format!("{:x}", Sha256::digest(&message));
    for chunk in [1usize, 7, 63, 64, 65, 128, 599] {
        let mut hasher = Sha256::new();
        for piece in message.chunks(chunk) {
            hasher.update(piece);
        }
        assert_eq!(format!("{:x}", hasher.finalize()), one_shot, "chunk size {chunk}");
    }
}
