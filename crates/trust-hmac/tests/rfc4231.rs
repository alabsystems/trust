// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Known-answer tests: **RFC 4231** *Identifiers and Test Vectors for
//! HMAC-SHA-224, HMAC-SHA-256, HMAC-SHA-384, and HMAC-SHA-512*, §4.
//!
//! All seven RFC 4231 cases are here, for both HMAC-SHA-256 and HMAC-SHA-512.
//! Two of them exist in this file for reasons specific to *this* tree:
//!
//! * **Cases 6 and 7 use a 131-byte key**, longer than the 64-byte SHA-256
//!   block, so they are the only coverage of RFC 2104's "hash the key first"
//!   branch. Neither consumer in this repository exercises it — both pass a
//!   32-byte key — so without these vectors that branch would ship untested.
//! * **Case 2's key is 4 bytes**, well under the block size, pinning the
//!   zero-padding branch that the consumers *do* use.
//!
//! Every expected value was re-checked against CPython's `hmac`/`hashlib`
//! (OpenSSL) before being written down.

use trust_hmac::{Hmac, Mac};
use trust_sha2::{Sha256, Sha512};

type HmacSha256 = Hmac<Sha256>;
type HmacSha512 = Hmac<Sha512>;

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("String write cannot fail");
    }
    out
}

fn unhex(text: &str) -> Vec<u8> {
    assert!(text.len() % 2 == 0, "hex literal must have an even length");
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[i * 2..i * 2 + 2], 16).expect("hex literal"))
        .collect()
}

fn repeated(byte: u8, count: usize) -> Vec<u8> {
    vec![byte; count]
}

fn tag_256(key: &[u8], data: &[u8]) -> String {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(data);
    format!("{:x}", mac.finalize().into_bytes())
}

fn tag_512(key: &[u8], data: &[u8]) -> String {
    let mut mac = HmacSha512::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(data);
    format!("{:x}", mac.finalize().into_bytes())
}

/// RFC 4231 §4.2 — 20-byte key, 8-byte data.
#[test]
fn case_1() {
    let key = repeated(0x0b, 20);
    let data = b"Hi There";
    assert_eq!(
        tag_256(&key, data),
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
    );
    assert_eq!(
        tag_512(&key, data),
        "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde\
         daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854"
    );
}

/// RFC 4231 §4.3 — a SHORT key (4 bytes), the branch both consumers take.
#[test]
fn case_2_short_key() {
    let key = b"Jefe";
    let data = b"what do ya want for nothing?";
    assert_eq!(
        tag_256(key, data),
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
    );
    assert_eq!(
        tag_512(key, data),
        "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea250554\
         9758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"
    );
}

/// RFC 4231 §4.4 — 50 bytes of data, so the inner hash spans two SHA-256
/// blocks once the 64-byte ipad block is prepended.
#[test]
fn case_3() {
    let key = repeated(0xaa, 20);
    let data = repeated(0xdd, 50);
    assert_eq!(
        tag_256(&key, &data),
        "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"
    );
    assert_eq!(
        tag_512(&key, &data),
        "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39\
         bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb"
    );
}

/// RFC 4231 §4.5 — a 25-byte key with no repeated structure.
#[test]
fn case_4() {
    let key = unhex("0102030405060708090a0b0c0d0e0f10111213141516171819");
    let data = repeated(0xcd, 50);
    assert_eq!(
        tag_256(&key, &data),
        "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"
    );
    assert_eq!(
        tag_512(&key, &data),
        "b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3db\
         a91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd"
    );
}

/// RFC 4231 §4.6 — the truncation case. This crate exposes no truncated
/// verifier (no call site wants one), so the full tag is checked and the
/// RFC's 128-bit prefix is checked separately.
#[test]
fn case_5_truncation_prefix() {
    let key = repeated(0x0c, 20);
    let data = b"Test With Truncation";
    let full = tag_256(&key, data);
    assert_eq!(full, "a3b6167473100ee06e0c796c2955552bfa6f7c0a6a8aef8b93f860aab0cd20c5");
    // RFC 4231's HMAC-SHA-256-128 expected value.
    assert_eq!(&full[..32], "a3b6167473100ee06e0c796c2955552b");
}

/// RFC 4231 §4.7 — **131-byte key**, longer than the SHA-256 block, so the key
/// is hashed first (RFC 2104 §3 / FIPS 198-1 §3 step 2). No consumer in this
/// tree reaches this branch; these two cases are its only coverage.
#[test]
fn case_6_long_key() {
    let key = repeated(0xaa, 131);
    let data = b"Test Using Larger Than Block-Size Key - Hash Key First";
    assert_eq!(
        tag_256(&key, data),
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
    );
    assert_eq!(
        tag_512(&key, data),
        "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f352\
         6b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598"
    );
}

/// RFC 4231 §4.8 — 131-byte key AND 152 bytes of data.
///
/// Note the SHA-512 answer here differs from the SHA-256 one in more than
/// width: SHA-512's block is 128 bytes, so a 131-byte key is long for *both*
/// families but by different margins, and both hash-the-key paths run.
#[test]
fn case_7_long_key_long_data() {
    let key = repeated(0xaa, 131);
    let data: &[u8] = b"This is a test using a larger than block-size key and a larger \
than block-size data. The key needs to be hashed before being used by the HMAC algorithm.";
    assert_eq!(data.len(), 152, "RFC 4231 case 7 data is 152 bytes");
    assert_eq!(
        tag_256(&key, data),
        "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"
    );
    assert_eq!(
        tag_512(&key, data),
        "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944\
         b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58"
    );
}

/// Key lengths around the block-size transition, generated with CPython's
/// `hmac` (OpenSSL) — a third implementation independent of this crate and of
/// the incumbent.
///
/// `key[i] = (i * 13 + 5) mod 256`. The interesting values are 63/64/65 for
/// SHA-256 (block 64) and 127/128/129 for SHA-512 (block 128): at exactly the
/// block size the key is used verbatim, one byte over and it is hashed.
#[test]
fn key_length_boundaries() {
    #[rustfmt::skip]
    let expectations: &[(usize, &str, &str)] = &[
        (0, "60818f537fe4d331cb0f81a3822fcc27889531f21c772bd1017515153dfaede3",
            "0879153870aa77a892f26b65118e580501356dcfb7dec03555b4722cb62442f283a66d0bde7a2c627cd3c5b1e4ba95b2d2b585ed0f346289268d27d0d758bdc8"),
        (1, "4c7c626e4a7994915f74f91b84be1b3517aed9f96bfa521f1839a299e121ade2",
            "582ef32c58af3fa9859bd08f131b4b6f06b994b7fa033490d88ba3558ae55c1228ddb1670e1f3169f36f307a40fe09b173301ef20f58343580786cfe21488951"),
        (63, "0c9828b3838533232fea7d8998e7f5bb089de44d4d2573e48d9d00a5985a7a48",
            "6146808ff407154de4d0193e8597224d71d9d0506f947e9c5825d62f757c6bfa0f828239ba2b573ef4c0042729abdb62cfdc97695a2b9a739af92f1d0803a74c"),
        // 64 = exactly the SHA-256 block: used verbatim, not hashed.
        (64, "e70ddd7bae7abe527920cc3a6e1c95475c76a74ac944b322c7c8d17ab46f6283",
            "f379120efe3e1b67243aea6b35a9ab106697de08ddadcb4b344a3e12dc5bec25071bd6fc99a70fff26dc1d07e34ab499d719c08900e5c9f695b182a03df8f903"),
        // 65 = one over: SHA-256 hashes the key, SHA-512 still does not.
        (65, "2c076dcd50b8bdd2e884077cae130a902cff0c9a0320c7ae2b70bebaacb578cf",
            "7725f151705ebe3d95ef61a24e3d3b8fdbb197b046cb4411b2a8684257347e42e89a1e54855793c4edd9711f2b115671e4f9870be5f434801aa7c22853452002"),
        (100, "13d7347ac8f42e587c3daa75065b0a5134c63a6e2276502138fc53d4ab7abbf3",
            "4610e44b06d4cac7bebb03acef267f4042787f5fb0c7ac0b7861cedcf7c033458f7c2701741cd2eadc2eeb252378bd48e195eae689d73e9d63c7f08323b880b1"),
        // 128 = exactly the SHA-512 block.
        (128, "458cf85cefaa6b42fc6c4bf632e863058f145a7a6f5a0b3e30c0b36f35dc239d",
            "df48b40c88e0b25efac2373e9ed897bbec45dff10a90516eec62e750f2c190d1ff136ee6fcea278fc8526c371644e99110c8809d3286fab39b120bc35fa65fd4"),
        // 129 = one over: now SHA-512 hashes the key too.
        (129, "e0953dfb78e95bc1f0d4c234dd2dedb0952cb40eea1818e3e0a105650ff4329e",
            "00dbe08fc07b918e418de8f5f92372c5fbbd8e8a3e88358f6e50cf6cd1f7de83adc6ef01ac514b539f0b5211d673f4d2d802d7032b0973f78e77617ff4f3a961"),
    ];

    for &(key_length, expected_256, expected_512) in expectations {
        let key: Vec<u8> = (0..key_length).map(|i| ((i * 13 + 5) & 0xff) as u8).collect();
        let data = b"boundary-key-probe";
        assert_eq!(tag_256(&key, data), expected_256, "HMAC-SHA256 with a {key_length}-byte key");
        assert_eq!(tag_512(&key, data), expected_512, "HMAC-SHA512 with a {key_length}-byte key");
    }
}

/// `verify_slice` must accept the tag the MAC itself produced, and reject
/// everything else — including a tag of the wrong length.
#[test]
fn verify_slice_accepts_only_the_right_tag() {
    let key = repeated(0x0b, 20);
    let data = b"Hi There";
    let expected = unhex("b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7");

    let mut mac = HmacSha256::new_from_slice(&key).expect("any key length");
    mac.update(data);
    assert!(mac.verify_slice(&expected).is_ok(), "the RFC 4231 tag must verify");

    // Every single-bit flip must be rejected.
    for byte_index in 0..expected.len() {
        for bit in 0..8 {
            let mut corrupted = expected.clone();
            corrupted[byte_index] ^= 1 << bit;
            let mut mac = HmacSha256::new_from_slice(&key).expect("any key length");
            mac.update(data);
            assert!(
                mac.verify_slice(&corrupted).is_err(),
                "flipping bit {bit} of byte {byte_index} must fail verification"
            );
        }
    }

    // Wrong length: short, long, and empty.
    let mut too_long = expected.clone();
    too_long.push(0);
    for wrong in [&expected[..31], &expected[..0], &too_long[..]] {
        let mut mac = HmacSha256::new_from_slice(&key).expect("any key length");
        mac.update(data);
        assert!(mac.verify_slice(wrong).is_err(), "a {}-byte tag must fail", wrong.len());
    }

    // Wrong data.
    let mut mac = HmacSha256::new_from_slice(&key).expect("any key length");
    mac.update(b"Hi There!");
    assert!(mac.verify_slice(&expected).is_err());

    // Wrong key.
    let mut mac = HmacSha256::new_from_slice(&repeated(0x0c, 20)).expect("any key length");
    mac.update(data);
    assert!(mac.verify_slice(&expected).is_err());
}

/// `update` must be chunk-boundary independent, exactly as the hash is.
///
/// `trust_buildcache::integrity::update_entry_hmac` feeds a MAC from a 64 KiB
/// read loop interleaved with 1- and 8-byte framing pushes, so this is the
/// shape the only streaming consumer actually uses.
#[test]
fn incremental_updates_are_chunk_independent() {
    let key = repeated(0x5a, 32);
    let data: Vec<u8> = (0..500).map(|i| ((i * 7 + 3) & 0xff) as u8).collect();

    let reference = tag_256(&key, &data);
    for chunk in 1..=140usize {
        let mut mac = HmacSha256::new_from_slice(&key).expect("any key length");
        for piece in data.chunks(chunk) {
            mac.update(piece);
        }
        assert_eq!(
            format!("{:x}", mac.finalize().into_bytes()),
            reference,
            "HMAC-SHA256 depends on chunk size {chunk}"
        );
    }

    // Empty updates must be no-ops, including a MAC that receives nothing.
    let mut mac = HmacSha256::new_from_slice(&key).expect("any key length");
    mac.update(b"");
    mac.update(b"");
    assert_eq!(format!("{:x}", mac.finalize().into_bytes()), tag_256(&key, b""));
}
