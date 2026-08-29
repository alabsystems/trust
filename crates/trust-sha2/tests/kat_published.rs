// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Known-answer tests **organised by provenance**.
//!
//! A KAT is only as good as the answer it compares against, and the failure
//! mode that matters here is not a wrong implementation — it is a *self-derived*
//! expectation. A table produced by running the code under test proves the code
//! is deterministic and nothing else. So every expected value below is labelled
//! with where it came from, and the two tiers are kept mechanically separate.
//!
//! # Tier P — PUBLISHED
//!
//! | Source | What it pins | Where |
//! |---|---|---|
//! | **NIST CAVP** `SHA{224,256,384,512}ShortMsg.rsp` | every byte length `0..=64` (SHA-224/256) and `0..=128` (SHA-384/512), contiguously — so **every padding-boundary length is a published answer**, including 55/56/63/64 and 111/112/127/128 | vendored in `tests/data/`, see `tests/data/PROVENANCE.md` |
//! | **NIST CAVP** `SHA{256,512}Monte.rsp` | 100 checkpoints × 1000 chained iterations = 100,000 dependent hashes per algorithm | vendored in `tests/data/` |
//! | **NIST CAVP** `Len = 0` records | the empty message, all four widths | inline, `cavp_empty_message` |
//! | **RFC 6234 §8.5** (identical values to **FIPS PUB 180-4** Appendices A–D) | `"abc"`, the 448-bit and 896-bit sample messages, 1,000,000 × `'a'`, and a 640-byte exact-block-multiple message | inline below, each row citing its RFC 6234 `TEST` name |
//!
//! Every inline tier-P literal was checked three ways before it was committed:
//! recomputed with CPython `hashlib`, searched for **in the RFC 6234 text
//! itself**, and (for the CAVP rows) recomputed from the vendored file. That
//! check is what moved four rows out of tier P — see
//! [`derived_cross_width_sample_messages`] — and it caught one transcription
//! error in a SHA-512 literal that would otherwise have shipped as a red test.
//!
//! # Tier D — DERIVED (repeated-byte padding boundaries, and four unpublished pairs)
//!
//! The task that produced this file asks for **repeated-byte** messages at the
//! padding boundaries. NIST publishes no repeated-byte vector at those lengths
//! (CAVP's messages are pseudorandom), so those rows are *not* published and are
//! labelled `DERIVED`, never `CAVP`. Their expected values were produced by
//! CPython 3.9 `hashlib` (OpenSSL) — an implementation independent of both this
//! crate and the incumbent — and
//! [`derived_rows_are_reproduced_by_the_incumbent_sha2_crate`] re-derives every
//! one of them from the incumbent `sha2` crate **on each test run**, so the
//! label is enforced by the suite rather than asserted in a comment.
//!
//! Read that as: tier D is a two-implementation cross-check (OpenSSL at
//! authoring time, `sha2` at run time). Tier P is a *standards body's* answer.
//! They are not the same kind of evidence and this file does not blur them.
//!
//! # What this file adds over `kat.rs` and `boundary.rs`
//!
//! `kat.rs` carries the FIPS appendix vectors and `boundary.rs` carries
//! OpenSSL-generated boundary values over a pseudorandom message. Neither had a
//! *published* answer at a padding boundary. This file does, for all four
//! digest widths, and it states which rows are which.

#![allow(clippy::needless_range_loop)]

use trust_sha2::{Digest, Sha224, Sha256, Sha384, Sha512};

// ===========================================================================
// Vendored CAVP data. `include_str!` and not a runtime file read on purpose:
// a missing vector file must be a BUILD error, not a test that silently checks
// nothing. A silent instrument reads as a clean result.
// ===========================================================================

const SHA224_SHORT_MSG: &str = include_str!("data/SHA224ShortMsg.rsp");
const SHA256_SHORT_MSG: &str = include_str!("data/SHA256ShortMsg.rsp");
const SHA384_SHORT_MSG: &str = include_str!("data/SHA384ShortMsg.rsp");
const SHA512_SHORT_MSG: &str = include_str!("data/SHA512ShortMsg.rsp");
const SHA256_MONTE: &str = include_str!("data/SHA256Monte.rsp");
const SHA512_MONTE: &str = include_str!("data/SHA512Monte.rsp");

/// `(file name, SHA-256 of the file as vendored, expected record count)`.
///
/// The digests were computed by `shasum -a 256` (OpenSSL) at vendoring time and
/// are recorded in `tests/data/PROVENANCE.md`. Re-checking them here catches the
/// one failure this suite could not otherwise see: a vector file edited or
/// truncated so that the KAT set shrinks while every remaining row still passes.
const CAVP_FILE_DIGESTS: &[(&str, &str, &str)] = &[
    (
        "SHA224ShortMsg.rsp",
        "0dad6656c08f77252f6ccb789e42284fd61fc53bba30e83162800aa3d2aa939f",
        SHA224_SHORT_MSG,
    ),
    (
        "SHA256ShortMsg.rsp",
        "75e1cb83994638481808e225b9eb0c1ebd0c232d952ac42b61abce6363be283c",
        SHA256_SHORT_MSG,
    ),
    (
        "SHA384ShortMsg.rsp",
        "7ea7bcf00fadc20949fae63703e40681ddf288fea808471cb3cbc95f3ec16811",
        SHA384_SHORT_MSG,
    ),
    (
        "SHA512ShortMsg.rsp",
        "e53a36c03609e5a3e3cc4b6e117a499db7864c23ec825c6cec99503a45f40764",
        SHA512_SHORT_MSG,
    ),
    (
        "SHA256Monte.rsp",
        "29ea30c6bb4b84e425fb8c1d731c6bb852dac935825f2bd1143e5d3c4f10bfb9",
        SHA256_MONTE,
    ),
    (
        "SHA512Monte.rsp",
        "8ca78659286c2f01667a98fc7accd32fc171ae7b24ac00f1a8ce6b77770247fa",
        SHA512_MONTE,
    ),
];

// ===========================================================================
// Helpers
// ===========================================================================

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(&mut out, "{byte:02x}").expect("String write cannot fail");
    }
    out
}

fn unhex(text: &str) -> Vec<u8> {
    assert!(text.len() % 2 == 0, "hex literal must have an even length: {text:?}");
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[i * 2..i * 2 + 2], 16).expect("hex literal"))
        .collect()
}

fn digest_hex<D: Digest>(message: &[u8]) -> String {
    hex(D::digest(message).as_ref())
}

// ===========================================================================
// The CAVS .rsp format
// ===========================================================================

/// One `ShortMsg` record: message bytes and the published digest.
struct ShortMsgRecord {
    /// Message length in BYTES (the file states it in bits).
    len: usize,
    message: Vec<u8>,
    expected: String,
}

/// Parse a CAVS `ShortMsg` response file.
///
/// # The one trap in this format
///
/// The `Len = 0` record prints `Msg = 00`. That single byte is a placeholder,
/// **not** the message: the message is empty. A parser that takes `Msg` at face
/// value silently tests `[0x00]` against the empty message's digest and fails
/// for the wrong reason — or, worse, a parser that "fixes" it by trusting `Msg`
/// and ignoring `Len` would drop the empty-input case entirely. `Len` is
/// authoritative and the record is cross-checked against it.
fn parse_short_msg(text: &str) -> Vec<ShortMsgRecord> {
    let mut records = Vec::new();
    let (mut len_bits, mut msg_hex) = (None, None);
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with('[') {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else { continue };
        let (key, value) = (key.trim(), value.trim());
        match key {
            "Len" => len_bits = Some(value.parse::<usize>().expect("Len is a decimal bit count")),
            "Msg" => msg_hex = Some(value.to_owned()),
            "MD" => {
                let bits = len_bits.take().expect("MD without a preceding Len");
                let raw = msg_hex.take().expect("MD without a preceding Msg");
                assert!(bits % 8 == 0, "byte-oriented vectors only: Len = {bits}");
                let len = bits / 8;
                // See the doc comment: Len == 0 means the empty message.
                let message = if len == 0 { Vec::new() } else { unhex(&raw) };
                assert_eq!(message.len(), len, "CAVP record Len disagrees with Msg");
                records.push(ShortMsgRecord { len, message, expected: value.to_owned() });
            }
            _ => {}
        }
    }
    records
}

/// Run one whole `ShortMsg` file and return the byte lengths it covered.
fn check_short_msg<D: Digest>(text: &str, label: &str) -> Vec<usize> {
    let records = parse_short_msg(text);
    assert!(!records.is_empty(), "{label}: parsed ZERO records — the parser or the file is broken");
    let mut lengths = Vec::with_capacity(records.len());
    for record in &records {
        assert_eq!(
            digest_hex::<D>(&record.message),
            record.expected,
            "{label} disagrees with NIST CAVP at message length {} bytes",
            record.len
        );
        lengths.push(record.len);
    }
    lengths
}

/// Parse a CAVS `Monte` response file: one seed, then `COUNT`/`MD` checkpoints.
fn parse_monte(text: &str) -> (Vec<u8>, Vec<String>) {
    let mut seed = Vec::new();
    let mut checkpoints = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        let Some((key, value)) = line.split_once('=') else { continue };
        match key.trim() {
            "Seed" => seed = unhex(value.trim()),
            "MD" => checkpoints.push(value.trim().to_owned()),
            _ => {}
        }
    }
    (seed, checkpoints)
}

/// The CAVS Monte Carlo procedure (SHAVS §6.4).
///
/// ```text
/// MD[0] = MD[1] = MD[2] = Seed
/// for j in 0..100:
///     for i in 3..=1002:  MD[i] = SHA(MD[i-3] || MD[i-2] || MD[i-1])
///     output MD[1002]; MD[0] = MD[1] = MD[2] = MD[1002]
/// ```
fn run_monte<D: Digest>(text: &str, label: &str) {
    let (seed, checkpoints) = parse_monte(text);
    assert!(!seed.is_empty(), "{label}: no Seed parsed");
    assert_eq!(checkpoints.len(), 100, "{label}: expected 100 Monte checkpoints");

    let mut a = seed.clone();
    let mut b = seed.clone();
    let mut c = seed;
    for (j, expected) in checkpoints.iter().enumerate() {
        for _ in 3..=1002 {
            let mut hasher = D::new();
            hasher.update(&a);
            hasher.update(&b);
            hasher.update(&c);
            let next = hasher.finalize().as_ref().to_vec();
            a = b;
            b = c;
            c = next;
        }
        assert_eq!(&hex(&c), expected, "{label} Monte checkpoint {j} disagrees with NIST CAVP");
        a = c.clone();
        b = c.clone();
    }
}

// ===========================================================================
// Tier P — NIST CAVP ShortMsg, all four widths
// ===========================================================================

#[test]
fn cavp_sha224_short_msg() {
    let lengths = check_short_msg::<Sha224>(SHA224_SHORT_MSG, "SHA-224");
    assert_eq!(lengths, (0..=64).collect::<Vec<_>>(), "SHA224ShortMsg.rsp lost records");
}

#[test]
fn cavp_sha256_short_msg() {
    let lengths = check_short_msg::<Sha256>(SHA256_SHORT_MSG, "SHA-256");
    assert_eq!(lengths, (0..=64).collect::<Vec<_>>(), "SHA256ShortMsg.rsp lost records");
}

#[test]
fn cavp_sha384_short_msg() {
    let lengths = check_short_msg::<Sha384>(SHA384_SHORT_MSG, "SHA-384");
    assert_eq!(lengths, (0..=128).collect::<Vec<_>>(), "SHA384ShortMsg.rsp lost records");
}

#[test]
fn cavp_sha512_short_msg() {
    let lengths = check_short_msg::<Sha512>(SHA512_SHORT_MSG, "SHA-512");
    assert_eq!(lengths, (0..=128).collect::<Vec<_>>(), "SHA512ShortMsg.rsp lost records");
}

/// The lengths the brief names, checked one at a time so a failure report says
/// *which* boundary broke instead of "somewhere in 65 records".
///
/// FIPS 180-4 §5.1.1: a SHA-224/256 message block is 64 bytes and the length
/// field is 8, so length `L` fits its padding in the same block iff
/// `L mod 64 <= 55`. §5.1.2: block 128, length field 16, so `L mod 128 <= 111`.
/// 55→56 and 111→112 are therefore the transitions; 63/64 and 127/128 are the
/// block-fill and exact-block-multiple neighbours.
#[test]
fn cavp_publishes_every_required_padding_boundary() {
    #[allow(clippy::type_complexity)]
    let lanes: &[(&str, &str, &[usize], fn(&[u8]) -> String)] = &[
        ("SHA-224", SHA224_SHORT_MSG, &[55, 56, 63, 64], digest_hex::<Sha224>),
        ("SHA-256", SHA256_SHORT_MSG, &[55, 56, 63, 64], digest_hex::<Sha256>),
        ("SHA-384", SHA384_SHORT_MSG, &[111, 112, 127, 128], digest_hex::<Sha384>),
        ("SHA-512", SHA512_SHORT_MSG, &[111, 112, 127, 128], digest_hex::<Sha512>),
    ];

    for &(label, text, required, compute) in lanes {
        let records = parse_short_msg(text);
        for &want in required {
            let record = records
                .iter()
                .find(|r| r.len == want)
                .unwrap_or_else(|| panic!("{label}: CAVP file has no {want}-byte record"));
            assert_eq!(
                compute(&record.message),
                record.expected,
                "{label} disagrees with NIST CAVP at the {want}-byte padding boundary"
            );
        }
        // The empty message is a boundary too: padding is the entire block.
        let empty = records.iter().find(|r| r.len == 0).expect("no Len = 0 record");
        assert!(empty.message.is_empty(), "the Len = 0 record must decode to an EMPTY message");
        assert_eq!(compute(&empty.message), empty.expected, "{label} disagrees on the empty input");
    }
}

// ===========================================================================
// Tier P — NIST CAVP Monte Carlo (chained state, 100,000 hashes per algorithm)
// ===========================================================================

#[test]
fn cavp_sha256_monte() {
    run_monte::<Sha256>(SHA256_MONTE, "SHA-256");
}

#[test]
fn cavp_sha512_monte() {
    run_monte::<Sha512>(SHA512_MONTE, "SHA-512");
}

// ===========================================================================
// Tier P — RFC 6234 §8.5 (== FIPS PUB 180-4 Appendices A/B/C/D)
// ===========================================================================
//
// RFC 6234 restates the FIPS 180-4 appendix examples in a machine-readable
// table; the values below are transcribed from that table (rfc-editor.org,
// SHA-256 of the fetched text
// 8f39f02a57bfd1da15634706724a585766e6223f77ecdaf243cad16cd3a1aa1b) and every
// one was recomputed with CPython `hashlib` before being written down.

/// RFC 6234 `TEST2_1` — the 448-bit (56-byte) sample message. FIPS 180-4 §A.2.
const TEST_448_BIT: &[u8] = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";

/// RFC 6234 `TEST2_2` — the 896-bit (112-byte) sample message. FIPS 180-4 §C.2.
const TEST_896_BIT: &[u8] =
    b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";

/// RFC 6234 `TEST4` repeated 10 times — 640 bytes, an exact multiple of 512
/// bits, so the padding lands in a block of its own with no message bytes.
fn test4_message() -> Vec<u8> {
    b"0123456701234567012345670123456701234567012345670123456701234567".repeat(10)
}

/// The empty message — PUBLISHED, but by **NIST CAVP**, not by RFC 6234.
///
/// RFC 6234's table has no plain empty-message row (its entry 5 is a
/// bit-oriented case with 5 bits of `0x68`). These four values are the
/// `Len = 0` records of the four vendored `ShortMsg` files, restated inline
/// because the brief names the empty input explicitly and because it is the
/// degenerate padding case: the message contributes nothing and the whole first
/// block is padding.
#[test]
fn cavp_empty_message() {
    assert_eq!(
        digest_hex::<Sha224>(b""),
        "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
    );
    assert_eq!(
        digest_hex::<Sha256>(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    assert_eq!(
        digest_hex::<Sha384>(b""),
        "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
    );
    assert_eq!(
        digest_hex::<Sha512>(b""),
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    );
}

#[test]
fn rfc6234_test1_abc() {
    assert_eq!(
        digest_hex::<Sha224>(b"abc"),
        "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
    );
    assert_eq!(
        digest_hex::<Sha256>(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        digest_hex::<Sha384>(b"abc"),
        "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
    );
    assert_eq!(
        digest_hex::<Sha512>(b"abc"),
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    );
}

/// RFC 6234 `TEST2_1` — the 448-bit message, at the **two widths the standard
/// publishes it for**.
///
/// FIPS 180-4 pairs the 448-bit message with SHA-224/256 (Appendices A.2, B.1)
/// and the 896-bit message with SHA-384/512 (Appendices C.2, D.2). RFC 6234's
/// table does the same. The other two widths of each message are therefore
/// **not published anywhere** and live in
/// [`derived_cross_width_sample_messages`], not here — checked mechanically:
/// every literal in this section was searched for in the RFC 6234 text before
/// being written down, and the four that were absent were moved out.
///
/// 56 bytes is exactly the SHA-224/256 padding transition (`56 mod 64 > 55`), so
/// this is a published boundary answer as well as an appendix example.
#[test]
fn rfc6234_test2_448_bit_message() {
    assert_eq!(TEST_448_BIT.len(), 56, "the 448-bit message is 56 bytes");
    assert_eq!(
        digest_hex::<Sha224>(TEST_448_BIT),
        "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525"
    );
    assert_eq!(
        digest_hex::<Sha256>(TEST_448_BIT),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
}

/// RFC 6234 `TEST2_2` — the 896-bit message, at the two widths the standard
/// publishes it for. 112 bytes is exactly the SHA-384/512 padding transition
/// (`112 mod 128 > 111`).
#[test]
fn rfc6234_test2_896_bit_message() {
    assert_eq!(TEST_896_BIT.len(), 112, "the 896-bit message is 112 bytes");
    assert_eq!(
        digest_hex::<Sha384>(TEST_896_BIT),
        "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039"
    );
    assert_eq!(
        digest_hex::<Sha512>(TEST_896_BIT),
        "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
    );
}

/// The four sample-message/width pairs that **no standard publishes** — DERIVED.
///
/// The brief asks for the 448-bit and 896-bit sample messages, and the natural
/// reading is "at every width". But FIPS 180-4 and RFC 6234 each pair the
/// 448-bit message with SHA-224/256 only and the 896-bit message with
/// SHA-384/512 only. Hashing the 448-bit message with SHA-512 produces a
/// perfectly good digest that **is not in any standard**, and filing it under
/// "FIPS 180-4 Appendix" would be a false provenance claim on a row that looks
/// exactly like its published neighbours. So these four are separated, labelled
/// DERIVED, and cross-checked against the incumbent alongside the tier-D rows.
///
/// They still earn their place: the 448-bit message at SHA-512 sits *below* the
/// 111-byte transition (one block), and the 896-bit message at SHA-256 spans two
/// blocks, so each covers a length class its published twin does not.
#[test]
fn derived_cross_width_sample_messages() {
    assert_eq!(
        digest_hex::<Sha384>(TEST_448_BIT),
        "3391fdddfc8dc7393707a65b1b4709397cf8b1d162af05abfe8f450de5f36bc6b0455a8520bc4e6f5fe95b1fe3c8452b"
    );
    assert_eq!(
        digest_hex::<Sha512>(TEST_448_BIT),
        "204a8fc6dda82f0a0ced7beb8e08a41657c16ef468b228a8279be331a703c33596fd15c13b1b07f9aa1d3bea57789ca031ad85c7a71dd70354ec631238ca3445"
    );
    assert_eq!(
        digest_hex::<Sha224>(TEST_896_BIT),
        "c97ca9a559850ce97a04a96def6d99a9e0e0e2ab14e6b8df265fc0b3"
    );
    assert_eq!(
        digest_hex::<Sha256>(TEST_896_BIT),
        "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
    );
}

/// RFC 6234 `TEST3` — 1,000,000 repetitions of `'a'`. FIPS 180-4 §A.3/§C.3.
#[test]
fn rfc6234_test3_million_a() {
    let message = vec![b'a'; 1_000_000];
    assert_eq!(
        digest_hex::<Sha224>(&message),
        "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67"
    );
    assert_eq!(
        digest_hex::<Sha256>(&message),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
    assert_eq!(
        digest_hex::<Sha384>(&message),
        "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985"
    );
    assert_eq!(
        digest_hex::<Sha512>(&message),
        "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b"
    );
}

/// RFC 6234 `TEST4` × 10 — 640 bytes, an exact multiple of the SHA-256 block
/// *and* of the SHA-512 block. Both families take the "padding gets its own
/// block" path here, at a length no other vector in this file uses.
#[test]
fn rfc6234_test4_exact_block_multiple() {
    let message = test4_message();
    assert_eq!(message.len(), 640);
    assert_eq!(message.len() % 64, 0, "exact SHA-256 block multiple");
    assert_eq!(message.len() % 128, 0, "exact SHA-512 block multiple");
    assert_eq!(
        digest_hex::<Sha224>(&message),
        "567f69f168cd7844e65259ce658fe7aadfa25216e68eca0eb7ab8262"
    );
    assert_eq!(
        digest_hex::<Sha256>(&message),
        "594847328451bdfa85056225462cc1d867d877fb388df0ce35f25ab5562bfbb5"
    );
    assert_eq!(
        digest_hex::<Sha384>(&message),
        "2fc64a4f500ddb6828f6a3430b8dd72a368eb7f3a8322a70bc84275b9c0b3ab00d27a5cc3c2d224aa6b61a0d79fb4596"
    );
    assert_eq!(
        digest_hex::<Sha512>(&message),
        "89d05ba632c699c31231ded4ffc127d5a894dad412c0e024db872d1abd2ba8141a0f85072a9be1e2aa04cf33c765cb510813a39cd5a84c4acaa64d3f3fb7bae9"
    );
}

// ===========================================================================
// Tier D — DERIVED: repeated-byte messages at the padding boundaries
// ===========================================================================
//
// PROVENANCE: NOT published. Message is `[fill; len]`. Expected values were
// produced by CPython 3.9 `hashlib` (OpenSSL) and are re-derived from the
// incumbent `sha2` crate by the test that follows the tables.
//
// Why keep these when tier P already covers the same lengths with published
// answers: a repeated byte makes every message a prefix of every longer one, so
// the digest at length 55 and the digest at length 56 differ *only* by the
// padding decision. A pseudorandom CAVP message changes the message bytes as
// well as the length, so it cannot isolate that. These rows can.

/// `(message length, fill byte, expected SHA-256)` — DERIVED, not published.
///
/// 55/56 is the FIPS 180-4 §5.1.1 transition; 63/64 the block fill and exact
/// block; 119/120 and 127/128 the same two transitions one block further in.
#[rustfmt::skip]
const DERIVED_SHA256: &[(usize, u8, &str)] = &[
    (0, 0xa5, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    (54, 0xa5, "380babbf1c79d0fa7f33527e410dce5257c0081b9103769b18717d6265c18fd3"),
    (55, 0xa5, "26ee0116778740a66fe2ba10ea063748b27306acc99188ec812746d4e8d70083"),
    (56, 0xa5, "4cf71e2b0aa0fcc0c271f68353026a77b8e50153632a8e4a73833cd64080e92e"),
    (57, 0xa5, "29235d912ef9b32094d9f48a075c12396f9c2a9b1fc9d72c222254959eceb4e6"),
    (63, 0xa5, "a1942663a5b8b93dffc9c4ff5f62c71a1c021d1fcc1e470dd46172abace1bca5"),
    (64, 0xa5, "bb626e5577021df95ea17eb6339e75904855b80087e40660931c4a89b302f74a"),
    (65, 0xa5, "667f84020d981fcedce2816e4e9969a02d5c317a0aef56a6c588175820f82a81"),
    (118, 0xa5, "8334bd21fb5581da18e287a8eaf2a703a72a4a5a61058eb5fa6cbde7a077cb54"),
    (119, 0xa5, "d4f197a1127980fe239c189bab09428d00de243c790ea7cad66f03928d992c89"),
    (120, 0xa5, "2065fa2ca0929999a6887714ef1af9d994cd93ab5ea165d4b426d7dc34f1e226"),
    (127, 0xa5, "bcc0ed0d968974b0fcba8a5fa9eef960a0c50803f14a65ea06fba1ed4b6f75f2"),
    (128, 0xa5, "39557315215be0f6922cec45d29336c8f72198032cababdc5ec0672d45e894ad"),
    (129, 0xa5, "0d4df645e098e323828009a90258def0ec1a596a54fe023e76a1bc05992eba61"),
    (55, 0x00, "02779466cdec163811d078815c633f21901413081449002f24aa3e80f0b88ef7"),
    (56, 0x00, "d4817aa5497628e7c77e6b606107042bbba3130888c5f47a375e6179be789fbb"),
    (63, 0x00, "c7723fa1e0127975e49e62e753db53924c1bd84b8ac1ac08df78d09270f3d971"),
    (64, 0x00, "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"),
    (55, 0xff, "aadaed00a3c5fbb8072ae7f1984ba8199fbe5272de427d11eaf31583af37db51"),
    (56, 0xff, "528ff50ab05e77bbbd224a9ec86165dbb6824a9a9efb544be0a1d57d5b416457"),
    (63, 0xff, "d12449c8124182545ae91924286cc6af13528bcf62a5ddbd5e00b891fffc1b48"),
    (64, 0xff, "8667e718294e9e0df1d30600ba3eeb201f764aad2dad72748643e4a285e1d1f7"),
];

/// `(message length, fill byte, expected SHA-512)` — DERIVED, not published.
///
/// 111/112 is the FIPS 180-4 §5.1.2 transition (16-byte length field);
/// 127/128 the block fill and exact block; 239/240 the transition repeated.
#[rustfmt::skip]
const DERIVED_SHA512: &[(usize, u8, &str)] = &[
    (0, 0xa5, "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"),
    (110, 0xa5, "8489f55b0a51ad78f821704c6cb0a2bff0e327b39be6e79643efaecc1d6fd2a15c0902a15f8f7ee47e25ad49a8724988329f497c1575a704253ce92c4553d22f"),
    (111, 0xa5, "7e243415d4b225ddf687968cc1bea6563b138e4c41a45fc6d326b9eb019329fa2bfb5c3cde64032d4b4f906509b6ba810d243302d28987987e8c36ec12af7e59"),
    (112, 0xa5, "dc227c6ddbedd9e0f8f74623c542d48affeae00cc991109d8b8f53a8cbc563e0588823e42f1a4d3a6048e2fa61b24c5108768a7a9465ed02a5726f0068aa1566"),
    (113, 0xa5, "c140386796aa6ca9795f688e5f5e5c52be68c4a664c3d5f8c7de7b20d4d2d6c549321b0cf4f33cb1de13bf91d2c5a9dbb794549902e7f2ced5d3c55f1aa106c3"),
    (118, 0xa5, "688fc0c0f8e56071d7b826b92a4a67ed2c42c7d0f073d19d2806ccfe1560d4e9f89fd398864ee8525a867cbe296fd45e143ac528e0dc9807e5b7cf52c2c91742"),
    (119, 0xa5, "9ef0070aca4cf113ab3077f44d59ec1ad05e57532d0dc235603be2ec515bce6c95620ec27e40c2cbec693e9ec06f267b996dc2cced4f87ccbc54b06d6d8e12d1"),
    (120, 0xa5, "92559b99b2a243754d87d42c9673606dfd846af58deb850d97a53f24cfb0f4c8c05bc864e9e8d8cca9f365d3157d20e3a6f8d5c3b5a5d45c0d892f99acd30e82"),
    (126, 0xa5, "f9d45279280de8d43dbf2226a11f0a24ffdd05c7b2ae97d636195c97a3ee181fc76d0b265ea295ecdabb45a2a9a0a53fd0c678bae7c049a739da091449655fee"),
    (127, 0xa5, "b9c376cefdbdc05fdbb030f0b3a90a08422d16bcfdb9000877b499a95b06ea1a245d908e582e768d8477f8203c121297c4ccda8e3651e0dda6fe0bc948f3ee20"),
    (128, 0xa5, "1cd2659b031e8a279f8888ec96a79d5bf570189c301bef9270358815587d80ad95b59b2e707f5bf7619b2eb7f99faaaf3a18cda9d62a38463c7e8a2fdada8a58"),
    (129, 0xa5, "49b3090cd8c826d1aacc4250f0961bc771f9ce89b8d1c5b8c3799105b69594a93f0fb2e6746ac7aaa03dad92862a8c5632193ccb2f1bafaa550fa47b1fdf0a25"),
    (239, 0xa5, "4c6c45f0c04c8434d46ce884df50b4bb1ec4f320face54fcf2c1c229af5513e683edb560b454902c8ef6ea953cfab87956faa09a2983df8ef81105019b6b19f0"),
    (240, 0xa5, "cb3dd6768892f60303562b477818bfb2cbb448fb1ec9bd36ff4d964a93c6a04eef2715b9169a334bc324ac2a255557a9663dc6571fdc1b09b11101c9e171590f"),
    (111, 0x00, "77ddd3a542e530fd047b8977c657ba6ce72f1492e360b2b2212cd264e75ec03882e4ff0525517ab4207d14c70c2259ba88d4d335ee0e7e20543d22102ab1788c"),
    (112, 0x00, "2be2e788c8a8adeaa9c89a7f78904cacea6e39297d75e0573a73c756234534d6627ab4156b48a6657b29ab8beb73334040ad39ead81446bb09c70704ec707952"),
    (127, 0x00, "876fee26a8dc66d652341b4951d4a96f4f2652803231ed5ec625bbe0d5c49ea70941f5299d775a1ace2291fc33b26016f73c81acde83b3c495be55b6916890a1"),
    (128, 0x00, "ab942f526272e456ed68a979f50202905ca903a141ed98443567b11ef0bf25a552d639051a01be58558122c58e3de07d749ee59ded36acf0c55cd91924d6ba11"),
    (111, 0xff, "ab0843dec43271ce45b21ac736670d67878bf765f08f8285f3c3de8215e45c3075edcb7fc648e5670bf8ae3450af222fdff789212f6b0000d0309ce4db088432"),
    (112, 0xff, "91078b0922e575edeb26558219603518141f167d6edeb7dfd56225beddd5482b0ab282d4feccffbe52eeb8fa0eff9b9d331c5fc55ad0d1d4b1b71cb29f2a0060"),
    (127, 0xff, "7dbc293d166b86387b18ff968d3129904059ac4df07da056d77497af61e8e2fe9ae6b8ee09733dd87b879078076d0dade6439cf7054200449d3da677cd02a36a"),
    (128, 0xff, "5acaf06f5dd1d107b81b9b7516d454e304cf5699d01ffe66a01ad554cfb0db896bbc16e08bd4fbcab36364909edf50ecb6c8042722a4c59456d9048244cd57f0"),
];

// ===========================================================================

#[test]
fn derived_repeated_byte_padding_boundaries_sha256() {
    for &(len, fill, expected) in DERIVED_SHA256 {
        let message = vec![fill; len];
        assert_eq!(
            digest_hex::<Sha256>(&message),
            expected,
            "SHA-256 disagrees on {len} bytes of 0x{fill:02x}"
        );
    }
}

#[test]
fn derived_repeated_byte_padding_boundaries_sha512() {
    for &(len, fill, expected) in DERIVED_SHA512 {
        let message = vec![fill; len];
        assert_eq!(
            digest_hex::<Sha512>(&message),
            expected,
            "SHA-512 disagrees on {len} bytes of 0x{fill:02x}"
        );
    }
}

/// The DERIVED label, enforced.
///
/// This is what makes the tier-D rows a *cross-implementation* claim instead of
/// a snapshot: the incumbent recomputes every row here, at run time, from the
/// same inputs. It is also the acceptance gate the replacement has to pass.
///
/// **Delete this test together with the `sha2` dev-dependency** on the day the
/// incumbent leaves the graph. The static tables above survive that deletion and
/// keep their OpenSSL provenance.
#[test]
fn derived_rows_are_reproduced_by_the_incumbent_sha2_crate() {
    use sha2::Digest as IncumbentDigest;

    for &(len, fill, expected) in DERIVED_SHA256 {
        let message = vec![fill; len];
        let incumbent = <sha2::Sha256 as IncumbentDigest>::digest(&message);
        assert_eq!(
            hex(&incumbent),
            expected,
            "the DERIVED SHA-256 row for {len} bytes of 0x{fill:02x} is not what the incumbent computes"
        );
    }
    for &(len, fill, expected) in DERIVED_SHA512 {
        let message = vec![fill; len];
        let incumbent = <sha2::Sha512 as IncumbentDigest>::digest(&message);
        assert_eq!(
            hex(&incumbent),
            expected,
            "the DERIVED SHA-512 row for {len} bytes of 0x{fill:02x} is not what the incumbent computes"
        );
    }

    // The four unpublished sample-message/width pairs from
    // `derived_cross_width_sample_messages` carry the same label, so they get
    // the same enforcement.
    assert_eq!(
        hex(&<sha2::Sha384 as IncumbentDigest>::digest(TEST_448_BIT)),
        "3391fdddfc8dc7393707a65b1b4709397cf8b1d162af05abfe8f450de5f36bc6b0455a8520bc4e6f5fe95b1fe3c8452b"
    );
    assert_eq!(
        hex(&<sha2::Sha512 as IncumbentDigest>::digest(TEST_448_BIT)),
        "204a8fc6dda82f0a0ced7beb8e08a41657c16ef468b228a8279be331a703c33596fd15c13b1b07f9aa1d3bea57789ca031ad85c7a71dd70354ec631238ca3445"
    );
    assert_eq!(
        hex(&<sha2::Sha224 as IncumbentDigest>::digest(TEST_896_BIT)),
        "c97ca9a559850ce97a04a96def6d99a9e0e0e2ab14e6b8df265fc0b3"
    );
    assert_eq!(
        hex(&<sha2::Sha256 as IncumbentDigest>::digest(TEST_896_BIT)),
        "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
    );
}

/// A table can be silently emptied. Pin what it must contain.
#[test]
fn derived_tables_cover_the_required_lengths_and_fills() {
    for &want in &[55usize, 56, 63, 64] {
        for &fill in &[0x00u8, 0xa5, 0xff] {
            assert!(
                DERIVED_SHA256.iter().any(|&(l, f, _)| l == want && f == fill),
                "DERIVED_SHA256 lost the ({want} bytes, 0x{fill:02x}) row"
            );
        }
    }
    for &want in &[111usize, 112, 127, 128] {
        for &fill in &[0x00u8, 0xa5, 0xff] {
            assert!(
                DERIVED_SHA512.iter().any(|&(l, f, _)| l == want && f == fill),
                "DERIVED_SHA512 lost the ({want} bytes, 0x{fill:02x}) row"
            );
        }
    }
    // The SHA-256 table must also carry the second-block repeats, 119/120/127/128.
    for &want in &[119usize, 120, 127, 128] {
        assert!(
            DERIVED_SHA256.iter().any(|&(l, _, _)| l == want),
            "DERIVED_SHA256 lost the {want}-byte row"
        );
    }
}

// ===========================================================================
// The vector files themselves
// ===========================================================================

/// A vector file that has been edited or truncated is the one defect this suite
/// cannot otherwise notice: every surviving row would still pass.
///
/// The pinned digests were computed by `shasum -a 256` (OpenSSL) at vendoring
/// time — see `tests/data/PROVENANCE.md`. Checking them with `trust-sha2` is not
/// circular in a way that can hide anything: a broken hash fails the KATs above,
/// and a broken hash that still reproduced an OpenSSL digest over 10 KB of text
/// is not a failure mode worth modelling.
#[test]
fn vendored_cavp_files_match_their_pinned_digests() {
    for &(name, pinned, contents) in CAVP_FILE_DIGESTS {
        assert_eq!(
            digest_hex::<Sha256>(contents.as_bytes()),
            pinned,
            "vendored {name} is not the file recorded in tests/data/PROVENANCE.md"
        );
    }
}
