// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Known-answer tests **organised by provenance**.
//!
//! # Tier P — PUBLISHED
//!
//! | Source | What it pins |
//! |---|---|
//! | **RFC 4231 §4**, all 7 test cases × **all 4 widths** | the reference HMAC-SHA-2 vectors, including the 131-byte-key cases that are the only coverage of RFC 2104's "hash the key first" branch |
//! | **NIST CAVP** `HMAC.rsp`, `[L=28/32/48/64]` | key lengths *below*, *exactly at*, and *above* the block size for both block sizes (64 and 128), with 128-byte messages |
//!
//! Every tier-P row was transcribed **mechanically** from the source document —
//! the RFC 4231 text (`rfc-editor.org/rfc/rfc4231.txt`, SHA-256
//! `72178527ce93500e730bc8eb182b857e583096d652b64ece0879c52ba1df973b`) and the
//! CAVP `hmactestvectors.zip` (SHA-256
//! `418c3837d38f249d6668146bd0090db24dd3c02d2e6797e3de33860a387ae4bd`) — and
//! every one was recomputed with CPython `hmac`/`hashlib` (OpenSSL) before being
//! written down. Zero mismatches at authoring time across all 28 RFC values and
//! all 1275 CAVP rows in the four SHA-2 groups.
//!
//! Two things worth knowing about the sources:
//!
//! * **RFC 4231 §4.4 (Test Case 3) prints its `Key` line without the `=`.** That
//!   is a defect in the published text, not in the parser that read it; a
//!   `Key\s*=` regex silently drops case 3 and leaves a green suite with six
//!   cases in it. It is called out here because the next person to re-extract
//!   these vectors will hit it.
//! * **RFC 4231 Test Case 5 is published truncated to 128 bits** (it is the
//!   truncation case). Its rows are compared as a prefix of the full tag, and
//!   [`rfc4231_truncation_shape_is_what_the_rfc_says`] pins the fact that
//!   exactly one case is short — so a future edit cannot quietly turn a
//!   full-length comparison into a 128-bit one.
//!
//! # Tier D — DERIVED (repeated-byte message-length boundaries)
//!
//! No standard publishes an HMAC over a repeated byte at the padding
//! boundaries, so those rows are labelled DERIVED, produced with CPython
//! `hmac` (OpenSSL), and re-derived from the incumbent `hmac` crate on every run
//! by [`derived_rows_are_reproduced_by_the_incumbent_hmac_crate`].
//!
//! Why message-length boundaries matter for a MAC and not just for a hash: the
//! inner hash consumes `K0 XOR ipad` first, which is **exactly one block**, so a
//! message of length `n` lands the inner padding decision at the same residue a
//! bare hash would — `n mod 64` for SHA-256, `n mod 128` for SHA-512. The
//! boundaries are therefore the same numbers, and a padding bug in the hash
//! shows up here through a completely different code path.
//!
//! # What this file adds over `rfc4231.rs`
//!
//! `rfc4231.rs` carries the seven RFC cases for SHA-256 and SHA-512, and a
//! key-length table generated with OpenSSL. This file adds the SHA-224 and
//! SHA-384 columns of the same RFC cases, replaces the generated key-length
//! table with **published** CAVP rows at the same boundaries, and adds the
//! message-length boundaries the brief asks for.

use trust_hmac::{Hmac, Mac};
use trust_sha2::{Digest, Sha224, Sha256, Sha384, Sha512};

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
    assert!(text.len() % 2 == 0, "hex literal must have an even length");
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[i * 2..i * 2 + 2], 16).expect("hex literal"))
        .collect()
}

/// One-shot tag, hex, for any `trust-sha2` digest.
fn tag<D: Digest>(key: &[u8], data: &[u8]) -> String {
    let mut mac = Hmac::<D>::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(data);
    hex(mac.finalize().into_bytes().as_ref())
}

// ===========================================================================
// Tier P — RFC 4231 §4
// ===========================================================================

/// One RFC 4231 test case. Hex exactly as the RFC prints it, with the
/// line-wrapping removed.
struct Rfc4231Case {
    case: u8,
    key: &'static str,
    data: &'static str,
    sha224: &'static str,
    sha256: &'static str,
    sha384: &'static str,
    sha512: &'static str,
}

#[rustfmt::skip]
const RFC4231: &[Rfc4231Case] = &[
    // RFC 4231 §4.2, Test Case 1 — key 20 B, data 8 B
    Rfc4231Case {
        case: 1,
        key: concat!("0b0b0b0b0b0b", "0b0b0b0b0b0b0b0b0b0b0b0b0b0b"),
        data: "4869205468657265",
        sha224: "896fb1128abbdf196832107cd49df33f47b4b1169912ba4f53684b22",
        sha256: "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
        sha384: "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6",
        sha512: "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854",
    },
    // RFC 4231 §4.3, Test Case 2 — key 4 B, data 28 B
    Rfc4231Case {
        case: 2,
        key: "4a656665",
        data: "7768617420646f2079612077616e7420666f72206e6f7468696e673f",
        sha224: "a30e01098bc6dbbf45690f3a7e9e6d0f8bbea2a39e6148008fd05e44",
        sha256: "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
        sha384: "af45d2e376484031617f78d2b58a6b1b9c7ef464f5a01b47e42ec3736322445e8e2240ca5e69e2c78b3239ecfab21649",
        sha512: "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737",
    },
    // RFC 4231 §4.4, Test Case 3 — key 20 B, data 50 B
    Rfc4231Case {
        case: 3,
        key: concat!("aaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa"),
        data: "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
        sha224: "7fb3cb3588c6c1f6ffa9694d7d6ad2649365b0c1f65d69d1ec8333ea",
        sha256: "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
        sha384: "88062608d3e6ad8a0aa2ace014c8a86f0aa635d947ac9febe83ef4e55966144b2a5ab39dc13814b94e3ab6e101a34f27",
        sha512: "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb",
    },
    // RFC 4231 §4.5, Test Case 4 — key 25 B, data 50 B
    Rfc4231Case {
        case: 4,
        key: concat!("010203040506", "0708090a0b0c0d0e0f10111213141516171819"),
        data: "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd",
        sha224: "6c11506874013cac6a2abc1bb382627cec6a90d86efc012de7afec5a",
        sha256: "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b",
        sha384: "3e8a69b7783c25851933ab6290af6ca77a9981480850009cc5577c6e1f573b4e6801dd23c4a7d679ccf8a386c674cffb",
        sha512: "b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3dba91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd",
    },
    // RFC 4231 §4.6, Test Case 5 — key 20 B, data 20 B
    Rfc4231Case {
        case: 5,
        key: concat!("0c0c0c0c0c0c", "0c0c0c0c0c0c0c0c0c0c0c0c0c0c"),
        data: "546573742057697468205472756e636174696f6e",
        sha224: "0e2aea68a90c8d37c988bcdb9fca6fa8",  // RFC prints this case TRUNCATED to 128 bits
        sha256: "a3b6167473100ee06e0c796c2955552b",  // RFC prints this case TRUNCATED to 128 bits
        sha384: "3abf34c3503b2a23a46efc619baef897",  // RFC prints this case TRUNCATED to 128 bits
        sha512: "415fad6271580a531d4179bc891d87a6",  // RFC prints this case TRUNCATED to 128 bits
    },
    // RFC 4231 §4.7, Test Case 6 — key 131 B, data 54 B
    Rfc4231Case {
        case: 6,
        key: concat!("aaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"),
        data: "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374",
        sha224: "95e9a0db962095adaebe9b2d6f0dbce2d499f112f2d2b7273fa6870e",
        sha256: "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
        sha384: "4ece084485813e9088d2c63a041bc5b44f9ef1012a2b588f3cd11f05033ac4c60c2ef6ab4030fe8296248df163f44952",
        sha512: "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598",
    },
    // RFC 4231 §4.8, Test Case 7 — key 131 B, data 152 B
    Rfc4231Case {
        case: 7,
        key: concat!("aaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"),
        data: "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e",
        sha224: "3a854166ac5d9f023f54d517d0b39dbd946770db9c2b95c9f6f565d1",
        sha256: "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2",
        sha384: "6617178e941f020d351e2f254e8fd32c602420feb0b8fb9adccebb82461e99c5a678cc31e799176d3860e6110c46523e",
        sha512: "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58",
    },
];

/// All seven RFC 4231 cases, all four widths.
///
/// Case 5 is published truncated to 128 bits, so its rows are compared as a
/// prefix; every other row is a full-length equality.
#[test]
fn rfc4231_all_cases_all_widths() {
    for c in RFC4231 {
        let key = unhex(c.key);
        let data = unhex(c.data);
        let lanes: [(&str, usize, &str, String); 4] = [
            ("HMAC-SHA-224", Sha224::OUTPUT_SIZE, c.sha224, tag::<Sha224>(&key, &data)),
            ("HMAC-SHA-256", Sha256::OUTPUT_SIZE, c.sha256, tag::<Sha256>(&key, &data)),
            ("HMAC-SHA-384", Sha384::OUTPUT_SIZE, c.sha384, tag::<Sha384>(&key, &data)),
            ("HMAC-SHA-512", Sha512::OUTPUT_SIZE, c.sha512, tag::<Sha512>(&key, &data)),
        ];
        for (label, output_size, expected, computed) in lanes {
            assert!(!expected.is_empty(), "case {}: no {label} value", c.case);
            assert!(
                expected.len() == 2 * output_size || expected.len() == 32,
                "case {}: {label} expectation is neither full-length nor the RFC's 128-bit truncation",
                c.case
            );
            assert_eq!(
                &computed[..expected.len()],
                expected,
                "RFC 4231 test case {} disagrees for {label}",
                c.case
            );
        }
    }
}

/// A truncated comparison is weaker than a full one, so the *shape* of the
/// table is pinned, not just its contents. Exactly one case (5, the truncation
/// case) may be short, and only to 128 bits.
#[test]
fn rfc4231_truncation_shape_is_what_the_rfc_says() {
    assert_eq!(RFC4231.len(), 7, "RFC 4231 §4 has seven test cases");
    let mut truncated = Vec::new();
    for c in RFC4231 {
        let short = [
            (c.sha224, 2 * Sha224::OUTPUT_SIZE),
            (c.sha256, 2 * Sha256::OUTPUT_SIZE),
            (c.sha384, 2 * Sha384::OUTPUT_SIZE),
            (c.sha512, 2 * Sha512::OUTPUT_SIZE),
        ];
        for (value, full) in short {
            if value.len() != full {
                assert_eq!(value.len(), 32, "case {}: unexpected expectation length", c.case);
                truncated.push(c.case);
            }
        }
    }
    assert_eq!(truncated, vec![5, 5, 5, 5], "only test case 5 is published truncated");
}

/// The RFC's cases must actually exercise all three key-normalization branches
/// of FIPS 198-1 §3, or the "hash the key first" path is untested and nothing
/// says so. Neither consumer in this tree reaches that branch.
#[test]
fn rfc4231_covers_all_three_key_branches() {
    let key_lengths: Vec<usize> = RFC4231.iter().map(|c| c.key.len() / 2).collect();
    assert!(key_lengths.iter().any(|&n| n < 64), "no key shorter than the SHA-256 block");
    assert!(key_lengths.iter().any(|&n| n > 64), "no key longer than the SHA-256 block");
    assert!(key_lengths.iter().any(|&n| n > 128), "no key longer than the SHA-512 block");
    assert!(key_lengths.contains(&131), "RFC 4231 cases 6 and 7 use a 131-byte key");
}

// ===========================================================================
// Tier P — NIST CAVP HMAC.rsp
// ===========================================================================
//
// Provenance: the CAVP HMAC validation vectors,
// https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/hmactestvectors.zip
// retrieved 2026-08-21, archive SHA-256
// 418c3837d38f249d6668146bd0090db24dd3c02d2e6797e3de33860a387ae4bd, file
// `HMAC.rsp` (CAVS 11.0).
//
// The file is 850 KB, too large to vendor for the value it adds over the
// `ShortMsg` files already in `trust-sha2/tests/data/`. What IS taken is the
// part no other source in this tree has: rows whose `Klen` sits below, exactly
// at, and above the block size, for BOTH block sizes. Two rows per distinct
// `Klen` per digest width, restricted to untruncated tags (`Tlen == L`), each
// citing its `Count`.
//
// Selection rule, stated so the subset is reproducible: within each `[L=..]`
// group, keep rows with `Tlen == L`, group by `Klen`, take the first two in file
// order. Every one of the 1275 rows in the four SHA-2 groups was verified
// against CPython `hmac` at extraction time; 0 mismatches.

struct CavpHmacCase {
    /// Digest size in bytes — the CAVP `[L=..]` group.
    l: usize,
    /// `Count` within the group, for citation.
    count: u32,
    /// Key length in bytes, restated so the boundary coverage test can read it.
    klen: usize,
    key: &'static str,
    msg: &'static str,
    mac: &'static str,
}

#[rustfmt::skip]
const CAVP_HMAC: &[CavpHmacCase] = &[
    // ---- HMAC.rsp [L=28]  (HMAC-SHA-224), block size 64 B, untruncated Tlen=28 rows ----
    // Klen = 50 (< block size 64: zero-padded)
    CavpHmacCase { l: 28, count: 60, klen: 50,
        key: concat!("cf127579d6b2", "b0b3a607a6314bf8733061c32a043593195527544f8753c65c7a70d05874f718275b88d0fa288bd3199813f0"),
        msg: "fa7e18cc5443981f22c0a5aba2117915f89c7781c34f61f9f429cb13e0fcd0ce947103be684ca869d7f125f08d27b3f2c21d59adc7ab1b66ded96f0b4fa5f018b80156b7a51ca62b60e2a66e0bc69419ebbf178507907630f24d0862e51bec101037f900323af82e689b116f427584541c8a9a51ac89da1ed78c7f5ec9e52a7f",
        mac: "354f87e98d276446836ea0430ce4529272a017c290039a9dfea4349b" },
    CavpHmacCase { l: 28, count: 61, klen: 50,
        key: concat!("82a289b0911f", "55c532e2571866fa354d973948ec7b899d573b833f00d53eb8d8bf65d50bcd8daaea54c5d628906e084a434d"),
        msg: "d06d296cad7d428b56b25c53fdfcf558b5bc4211ed31cfe63732678a4f23338b582225286881986247793056741c08c9698c0c05206ba3e4d692922a0f061d17da276e3d562b3b9075cba4bc003c5abbdc6106a68b3fe9cbf5b1bf01695dea38dfe6cc548064753c68117e2daa44345594a4fa9d3595e8c61df7b8b76410e315",
        mac: "5507c4c7c127046c04d161fdc75ec2f5122ed44e86679c39c69c5ae8" },
    // Klen = 55 (< block size 64: zero-padded)
    CavpHmacCase { l: 28, count: 135, klen: 55,
        key: concat!("b34a6eba59e6", "32e3c334df582fd0b03aca7f641c6914920a79943dca3998a86127f36bdab795c7424baf37f76018472305f0a983928386"),
        msg: "d03dd94e43d96ca459928aa96d2b81c35ed54566e33e66351fca406b7620727a9ee991f2f9d41da322deb306c6d085d9b509080a387decd6a6fe513232bb386a07063708975a72f72f9cc6e8cfa147f53af1ed8449ca8a6f8468ff62f384b084321b3559c47053e7a9542a1733a5af5f15155d9ebd2c2847e491b3c26385c20f",
        mac: "1c4944843c3ee7f98ab52987e0d2d4494aa72548bfdc3602db45b5f4" },
    CavpHmacCase { l: 28, count: 136, klen: 55,
        key: concat!("2fd5863ab5ac", "0109cd1cc8a6598e75d85811a84d0df14cd55e8b1cce7a5f65dfbe670deadaa8d43b2f06da067c5c6210baccd5ac44540a"),
        msg: "85c02d7cfab29f8adf0fa55ef36722a04757c8865053d2af3ba2f64e80aa958aba6e3625b655325cca2db00f686fd422f2c53423d0c98c2dc110b20c6e67cca1455cc0888401ecf994ec18ec9982a8814776169ef78ca0dafaa33e9a2df2d779cd92b4ee8d3c3529e655c33daf270584ed72573fec23787e8f638240e4d320da",
        mac: "eabba9f35ba39cfb9283390d5425687cdd70d4cb1fea433925647c79" },
    // Klen = 64 (== block size 64: used verbatim)
    CavpHmacCase { l: 28, count: 210, klen: 64,
        key: concat!("f3aa51ee90aa", "06e98e2388df7a3af2cd697f2a528f2a14140da405600b4a7b10076d0bb26c9d9ae66727d008f6dcca0f42140fb52ef3c6d930eb262160822de3"),
        msg: "2c070e5eb0a7efbfc40b234314c055fc436ce1e2300539b3784287fd3c4f947824c5e89aa3d933667dd4eb8587c33797ae6f0ccb3b8f95ad563dd940c8a7984d050775fa69d55b9ec23a19d40fc94fcf876a8eeddd96bb8ec3cab426ad353691d7b4ffa789012f119a28f45b333a6649d544b06f9d8271fcc7d162d7726338ed",
        mac: "695c328dc858a46be7ac8b8debf58dd9a9bd72d7a408a43e6bbc69a3" },
    CavpHmacCase { l: 28, count: 211, klen: 64,
        key: concat!("a27f5ba4a0d5", "a80cb4ef9bb18d4ffc4ad487680cb5a8f6c69cfe1b293cfacb67d670e101b803c1d904dd3c8fb2a3b40ad8a78055296091adbc1856d810e5deb8"),
        msg: "802ed28873c2160562fb9162246b60d75e2ffb8cecc5bb08831e9aec94f43be1735e2acfb8a26450e64a1a644a7ab26626800f3e0fad12d9946360d620706682229a9b076a7b05e0d690ff902f8c39944ef2009683e2c0e33733c71fcfc34b38d40baf9851f7029f7df4c9509a4afe4a1dac58fa0f0dcd10b3b6562f6996f2e9",
        mac: "ee63e86aac85f36961d697451288cf780041eafe462ca6557035d92a" },
    // Klen = 65 (> block size 64: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 28, count: 360, klen: 65,
        key: concat!("4b0f8fda0801", "7b10b647fcd6cd04f7870c92b2687574f238998c6008158e314d5db50634b8b511358cf07aebdcec01230f05e433f35f038d011f4293e3db2fad33"),
        msg: "2917cd5724319dcb5c08d917b67f25628d15543ff717d18249153d51dd92597e12ff271495eb4c2fdf74b911ff018a739a332e193018c9a9a0a2d6bdef581137454c94d5384d40054d5d5efabc6686ff7428c00b5f76ea96e7a25aacb936c440c9e45dc296c040f4afad11f97615e1ae24de523e0d99fcf126fc0f45c4923940",
        mac: "453b2373ce46595855f6030d243d1646293889416f05373e78126f59" },
    CavpHmacCase { l: 28, count: 361, klen: 65,
        key: concat!("289e2aece104", "8674bd571a4dac53043351a78964bda6fdf67e3fe36dd82f568d5275a86d750648cdd0c3e9a93fa8e00f6d46ce2d987380ae94401347132b5c8c23"),
        msg: "b453fc9e54122b181483005c4153cb8b47cef47a7499e307fe9f1eae484db1576102d372cdc1c646892aff8649a8872604eba16cb299ad4a55404ceb3690c58c71c7a88db36cb1c84340ee213f72245e2912703aa2c82ab474c60eadd6fb9eb2ec89c2178e7ab2454aae1554ac186bddbc2ba809c98e21ee6517ac1cb1f70372",
        mac: "01dafb716c50b09457ecc8778141ca84b645a232a4a39ed0230c7349" },
    // Klen = 66 (> block size 64: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 28, count: 285, klen: 66,
        key: concat!("5f448c3d3df6", "ceab97356819da0d459662b2d5a7366a5d46f2a6912a047264491b101f9cdde0b022d9844527bc401ac6c7a78fad80747e20a8b6cb416e303d8ee2ff"),
        msg: "d52fce9d1822001f8a252e34b4adc81831f9da370fec929d791cfdae93271117a646f0047d246b940ff0c5895eb0ba459ed9c0f29a1d8d005485d9d4ebbf65bec2b93c2cdf6f391e9101c9da5608f2e1fb2a952105ecf06c50c86629f680834a72b13b7e06ab72a75a80c28e655b78d59013df2e1900c2cbb60e2c167c0f72a1",
        mac: "1b3459ef88671f031be60252701231fec17132a0baa75d13938fbc9a" },
    CavpHmacCase { l: 28, count: 286, klen: 66,
        key: concat!("08e13bab5326", "369a2706c2b3e7e8f9b71cbe5646bd371aadae35efff8681cc6795be18bc269b1256014d7020343d46ef13fd2a127e81962b628c8e3d8268820578da"),
        msg: "9ee9136240b9c431747ba363a9b2b8363b1d57fb453898bcb7060821a80e9e94eda3f1a4ea69a7a7a81531a42874b670f7af4c1603cd6e7cad79ab441f069bf1e0b0174ba525a9046b44429bc2242b816c583e7b26715647c6c50482866f84c9a097ef1f1bf4b18ee48e3e1120c901b2c19f95f0572d386329717da385524165",
        mac: "f6f742b70c95ce5f69fa8ab727004ef546d6de9d8f05ad9f84a0210a" },
    // ---- HMAC.rsp [L=32]  (HMAC-SHA-256), block size 64 B, untruncated Tlen=32 rows ----
    // Klen = 40 (< block size 64: zero-padded)
    CavpHmacCase { l: 32, count: 30, klen: 40,
        key: concat!("9779d9120642", "797f1747025d5b22b7ac607cab08e1758f2f3a46c8be1e25c53b8c6a8f58ffefa176"),
        msg: "b1689c2591eaf3c9e66070f8a77954ffb81749f1b00346f9dfe0b2ee905dcc288baf4a92de3f4001dd9f44c468c3d07d6c6ee82faceafc97c2fc0fc0601719d2dcd0aa2aec92d1b0ae933c65eb06a03c9c935c2bad0459810241347ab87e9f11adb30415424c6c7f5f22a003b8ab8de54f6ded0e3ab9245fa79568451dfa258e",
        mac: "769f00d3e6a6cc1fb426a14a4f76c6462e6149726e0dee0ec0cf97a16605ac8b" },
    CavpHmacCase { l: 32, count: 31, klen: 40,
        key: concat!("09675f2dcc47", "83b599f18fb765583668a0fd8ae4096f6fcdc60d4f35b4130fbefcd542ffe7459d2a"),
        msg: "0cf2198c31376f5c8915660137725f2bbc180a986e5a7bda27fa81593a4a339bab92cbc39fb2b8581108ee48c794812d845a72ce8008c9e915d9e330bbb90e9136aa53ba0e6693dd4046d6b03362dfb9edfa04c887153cc5de677aab8c7839d517035879679c29727e96c5426324a2575fbe678d6cc7fef5eb6cebd595cfddef",
        mac: "6b142d4dfe217f1881aa0e6483b271dd5d43f70b85605953a0fef272ddde46ca" },
    // Klen = 45 (< block size 64: zero-padded)
    CavpHmacCase { l: 32, count: 75, klen: 45,
        key: concat!("b763263dc4fc", "62b227cd3f6b4e9e358c21ca036ce396ab9259c1bedd2f5cd90297dc703c336eca3e358a4d6dc5"),
        msg: "53cb09d0a788e4466d01588df6945d8728d9363f76cd012a10308dad562b6be093364892e8397a8d86f1d81a2096cfc8a1bbb26a1a75525ffebfcf16911dadd09e802aa8686acfd1e4524620254a6bca18dfa56e71417756e5a452fa9ae5aec5dc71591c11630e9defec49a4ecf85a14f60eb854657899972ea5bf6159cb9547",
        mac: "737301dea93db6bcbadd7bf796693961317ca680b380416f12f466f06526b36b" },
    CavpHmacCase { l: 32, count: 76, klen: 45,
        key: concat!("9fe42dfac92a", "4a136fa7c9f6e331b5d3a61aa73035b53a8d2517be43721b31b215a96b9bd43798cb5e8febfa97"),
        msg: "f9660fb784c14b5fbec280526a69c2294fba12aea163789bbe9f52a51b5aebb97d964f866c0d5e3be41820924fcf580db0725c7f210823cf7f45a0f964b14e5555070d1c3ddb2c281a80c7fbf72953031a4e771d7e521d578462cafae5a02ac8eb81f082e173ddadc8c41d964bbfda94f5180c8da28a8ebb33be77b0866fa798",
        mac: "7786c155d10c741b63ec650b7b1aa3bfd71ac71881ad06ae98fb082f17e0caa0" },
    // Klen = 64 (== block size 64: used verbatim)
    CavpHmacCase { l: 32, count: 120, klen: 64,
        key: concat!("992868504d25", "64c4fb47bcbd4ae482d8fb0e8e56d7b81864e61986a0e25682daeb5b50177c095edc9e971da95c3210c376e723365ac33d1b4f391817f4c35124"),
        msg: "ed4f269a8851eb3154771516b27228155200778049b2dc1963f3ac32ba46ea1387cfbb9c39151a2cc406cdc13c3c9860a27eb0b7fe8a7201ad11552afd041e33f70e53d97c62f17194b66117028fa9071cc0e04bd92de4972cd54f719010a694e414d4977abed7ca6b90ba612df6c3d467cded85032598a48546804f9cf2ecfe",
        mac: "2f8321f416b9bb249f113b13fc12d70e1668dc332839c10daa5717896cb70ddf" },
    CavpHmacCase { l: 32, count: 121, klen: 64,
        key: concat!("ceab398e4107", "483ede64ce107c9270e6022778b61f6a258d3b7045d4ad8506d32ece0a738d2cb948a562dbce8d7b66f30e6694d65ae439cffaa454af09abe449"),
        msg: "6dde9ae867e2feb367008a975d7853ed8f89690f3c87a1107f2e98aa7736f477a527ed64956f0d64c1b23361b261de78688ea865fcff113c84817e5b377e829cd2d25bcf3adbc06762cfda736f5390d01a49079d56e969f03313e6c703e3f942bb87ed0f9c4d9f25120085b5dc75ef5d6d618da0926d3293568dd7d8238de3d0",
        mac: "2d3a760595f3fb19293cc6d23651222a9f5a4f02284457a9c1ed4c43ac993ca5" },
    // Klen = 70 (> block size 64: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 32, count: 165, klen: 70,
        key: concat!("c09e29071c40", "5d5e820d345a46dbbf1e0f8202e92de3ed3e2d298e43aa4f846866e3b748990946d488c2c1ae5a6e99d32790d47d53d205481a497c936bf9ba29fa9c2821919f"),
        msg: "ea7240529980076d3b028a083ebc4e24efdaa06c9c84d76bf5b2d9fdb842e1038e487f5b30a5e010cddb4fcdb01ffc981eb0fcbc7d689207bc90ad36eef9b1ae38487a6dee929f3ff929f3357cb55253b7869a892b28f7e5fe386406a2776ed4b21d3b6e1c70cc6485947f27e9a5d8bd820380b9eced8e6b865206541be39fdc",
        mac: "49ae1c4a7a570fde47f7517ab18898b1b991d03cfcf8c45bb3615b5f755da682" },
    CavpHmacCase { l: 32, count: 166, klen: 70,
        key: concat!("bce50cdfff84", "3885d4f364d69f93bf58a2322c707b82e878eec96d11e5db97bbb54606a3a3ccc3bba716261070a6f759a70ed3cb785fd1354fe56648df11863669b70c803b7a"),
        msg: "93b7ef0e470ddfac6aef93c0dcd37b8f1c4baf5eadd978e3bf0512fa0baeb099ff9ec1061b6172479b5674db5606ffa7e6b5173309370e1647054aafd5904816bad5e1523032cccd4d786505e241ac83a484911189666f287553d6a8164e8dcb0c85d75c4e29f624c97ceea64a2c8b0c9ddfa560f70fa3ff91183e4b968f88a1",
        mac: "37f9f32918308210849dfebf8dd456804babd6845af07218f9d9be9df9743d55" },
    // Klen = 74 (> block size 64: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 32, count: 210, klen: 74,
        key: concat!("81574323c973", "540719d192833ddb51f13a52dcbae294aebea51be5f6aa47f3571f5d97facdcf0c7befbe809f44bdc73963d8514e4fd559774bb96087ef8eda6e7c64275d6d96c42b4e4e"),
        msg: "b9e944e0b42d0ff454f7f8aa24f00e9ee039058ce4094111e39731b6dc3ade2a4acec4cf9c5be078e4f10a72d3d685c1e5e4d5abd92cd07b64dff87f266f0853ddf1cd61d9c637a9b07ab0be32ecac119faf827218b17ad4541a27519477f76ed918089f54b63d0e1e5a92982979ac187764b5e989e066a61b1065340e9cd203",
        mac: "514bd18495f6de0e237054b8e3ba1a74c3fada4279ad6b8550f3a14712c528df" },
    CavpHmacCase { l: 32, count: 211, klen: 74,
        key: concat!("44f71c2317cd", "e52151c84260d1d3c04a28cc15ce5b3802b2e5357e2bfcaf10ab15d77dfaaad1a3883bada502939948234c559dcd95e7e158338fa12ac6fd21874ec2ffabed051416ef77"),
        msg: "2ac0bb0524c22b902de34ce64e6172d1b2074e159f517ab1abd152622cd10669f03aed8e2eb51c65bd0f38d084e288c532724e512fd558ddd257d2b1d41c5eb6040767803ddbb18b95a035c5d8492d4d35936b7b3630ee20f625b70f8e71d9dcd0efd0e3387d138c1f5eedce32dd88f223334b9a9eab65017f04aa8442179f62",
        mac: "ca0053d51f6cf6f9998ff1e0db00b90e82c7b18cb5377acc8ebe9afe20da1c3d" },
    // ---- HMAC.rsp [L=48]  (HMAC-SHA-384), block size 128 B, untruncated Tlen=48 rows ----
    // Klen = 50 (< block size 128: zero-padded)
    CavpHmacCase { l: 48, count: 45, klen: 50,
        key: concat!("5eab0dfa2731", "1260d7bddcf77112b23d8b42eb7a5d72a5a318e1ba7e7927f0079dbb701317b87a3340e156dbcee28ec3a8d9"),
        msg: "f41380123ccbec4c527b425652641191e90a17d45e2f6206cf01b5edbe932d41cc8a2405c3195617da2f420535eed422ac6040d9cd65314224f023f3ba730d19db9844c71c329c8d9d73d04d8c5f244aea80488292dc803e772402e72d2e9f1baba5a6004f0006d822b0b2d65e9e4a302dd4f776b47a972250051a701fab2b70",
        mac: "7cf5a06156ad3de5405a5d261de90275f9bb36de45667f84d08fbcb308ca8f53a419b07deab3b5f8ea231c5b036f8875" },
    CavpHmacCase { l: 48, count: 46, klen: 50,
        key: concat!("f86902e5e5db", "478ec6e278692728a812c4cd8745f90a7d9f7915f5a94345fc12d2770a3c94b01ffb9e0412999eb6261d11a0"),
        msg: "e0bcacbe96dad6f60e51129f35acd03e12276a91fa13fc15037c75cabb0aee3a19253bb8b35cc0e63208867a032c8f4150a066642f6ff9ea197dab7e9d6da67255c16e051a43bce174a489e85464693006f11a4c61135dce4187040937eb4d1c7eda6e2c315771f0bc6f4273911a07151c63afd3f8c8cec963e4a8f5ef4b8b3e",
        mac: "4bb4eb2db2cc921b159b78a2bb9edc1608bb2a1ca9873b411ae30a63386e462f9f69d9f5fc838ff1818748aab74da94f" },
    // Klen = 55 (< block size 128: zero-padded)
    CavpHmacCase { l: 48, count: 105, klen: 55,
        key: concat!("bfe6bb4c9b17", "1b93d28e9f8f86b88dbe509c66eed41818a1986d75b616fee4460f5456cd23667c8a9f1738289601519d33716a534db235"),
        msg: "5b7a078f980bb8919743bbce52fd0ba3c22083d2b0254e28c8d3a05def4da33bd64fb502cfb5d00ce03d49ad168dbe5d1c784a190c7dfa0685908558fe1e37725a4b2f4ebc7eca209c1f5f361b9f2d2393b9911c73f87da24a7a256221f3fb590ef4de3b066e8e16f3726432063a403d4f6dc2a48b9fbd443d17e84200d6d737",
        mac: "e82eeb7f4b7415a4c95dc82c46bb59715fda4e0bdaf64a7fb3af3c7058ec7d2a172b8293057b72f9664454e7dee11d95" },
    CavpHmacCase { l: 48, count: 106, klen: 55,
        key: concat!("4cf54eb8cf7b", "d421ddb0586ac4fab9c478cdaedd89cc5a195332211f7571b9988419843300fa1ded868d318f48909078bbf1839c8fed61"),
        msg: "d22f194a1af33cd8cdffe9967f677acb68500d6cbbf77a3f34f58840f0c16044827641dc43d6767ce98f85dd5cbeaa9fc5b28333e7f20df8b281cfa4156055e61555e04a1ceb5c5c93ba9210b2e89f6197f0a53996a2c091d16c3cd908d7059ab2545e5a4c39d6c0f10778f82bee43590993da4571107c51b83c35a6702e56a8",
        mac: "830b4a798f85c448b3d54abfee61b376597f65666d83a21052cb3f4466f44747431607bc659c91cb520308fbf4fcdb58" },
    // Klen = 128 (== block size 128: used verbatim)
    CavpHmacCase { l: 48, count: 165, klen: 128,
        key: concat!("b619d9d07461", "c11bc9fb66117d61ed90001366bbffdbff583556777584b0d65244af5c7bdbf3b7358d7c791b966cc809760e57398d1896ace72d26cc59a6904fcd92365edafb8af7986c7d90b2af3bfdbcdb1593c78fbe8e3378bbb0c519152bf9cb51c19a02a12a8fd35cb6f8b3ac337a828711d6c8e0c4c13e1e6af090cdae"),
        msg: "5a81e711adfe5077dd8c8b57c95e8e1f3de39f4fc448c523bd3e7c72b1fdacd6e489dc0d2a34a39ffc6460c1cb962b7a94a30c04b5426a75ffcfc69f0c4ba934d3a3da2e7935d56d6b9079a2a97b016d653a35c2cc0ce19124f887a617c951ce4e58493b4209cc294f983cc20b16f63fd52e8451b1ad13bf5342275079818deb",
        mac: "8b4258be4c094aa4056f332ede8c733772664b088ba22ef8caae7cefd77eceb35e83af8d9c1283cbbffe4a372b699c21" },
    CavpHmacCase { l: 48, count: 166, klen: 128,
        key: concat!("e48825a5503a", "6afe0bf9a240c67f27acd4a8f6993834645e03c80c72dd370cd2e10071a3ae18ef19bae9d697ea9a4118609190cd95361907a7fa1b58f499f3f5e79b935f12212f437dde399e3e6490244aa1f5e38ba9be2433b6ce924f6cc49e9f627321a5df9343fce1b59deb647d9a3ae00b234414ba7b4e020d67173be693"),
        msg: "8561865ac2ce12832746f82584a4b98e7f4c3ae2410e18196f4e3b475c62ae207d3cadbb1d490096519888db2f3f18e13bfb86f62216015cab8ea491ea734cd3b791a7e45e4f8e0b98d7955bba77e0372d4738161e0d5d84765d9e6a0d05a88e1aa89c5defa864e9e349462e8f14b9993d7a78cb9dbad69aba0551582ddf6958",
        mac: "ec780a915ec7deeba2c8c9e2ab15c9762a3eb18fafa2d48a554ae1fe6c4459da1a54e2d58bdf06fea0740098eebbb699" },
    // Klen = 130 (> block size 128: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 48, count: 225, klen: 130,
        key: concat!("74f41a6b1c4e", "5713499557d6f7e889f8a8ce2e444e8261fe6a8e5518769bdfa88188349a19b9f3a26db26675b3e40539c8c63b3a16286ddebbc539dbe817fba7866f9631204471cefdcbbf768cc9043006a6d4cb4ec2decf1c0c2ab35ad09f50ced0c896fa97d87e400aeb3f4a408ec5a993825fbcf7bdb8d48bb208956ed28ba0d4"),
        msg: "9a121482c7775a8b5fdaf1c2fb7de1a86ef931b1a88cf23ddbb47fc9dcfd0267cb173a6bf62b7c68fb6ff85b2df93e2539d1013f0a491aa9e991cf23e98656a082cb95f87c1b2cdd0eddb51048f94ad4aeeb48a426165321145a9b4ec3e85dff0755ac8f20ee71d2e24cb14a13280e9e15709147c499a68da23868b232cc1f6d",
        mac: "b0da90c043493511d94f22fac35b5962749c49972fb43571b8478764dffc1c25e3a7523fd405338a048d38dd1b75511d" },
    CavpHmacCase { l: 48, count: 226, klen: 130,
        key: concat!("d87fb6ba2721", "5e5cb65c3b5b34ac2a32037f30e1f7ea603d5a9bff8a330fe74bc70529596132f6334f36c0952dcf9c4c664ceb48f74539f3768a65c1535902085fd4fe138ab18172f1341893185a139773582c5e2c4369e4201143d12bc0074ba5d57d0f2c08c8c0a43e8d7e7db757bb34893a4a1d4db7b95f18e0e140adbcbba3f0"),
        msg: "9e1a5d9f236ef93f2cda60489166c82dce322327046644cc406b42e3005c2177f3b7af2a0159adcc8ba92f2cf413462e60b8db1ebb63de44febfa1b9adc87e79a480c0b814e3c17ac91c4f5eaef954ba929db6ed2c757df15d6d3430b66391993adb58f265f57c706d9d8785c7023df9ed497c3c5f8267fbe7dbc4f12213a100",
        mac: "3c7cee960221c9d9f7464aeb70d198bd60414dc3ffbfa7a2227a3a375ebb8f6448e524706e1e3ae95541bdcef2b31d9f" },
    // Klen = 145 (> block size 128: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 48, count: 285, klen: 145,
        key: concat!("f05d561f5ad7", "0403264c5e0a0edc12fd473b19c0b40f8cd85a99ba2a14987705876ab76359755b6c9ec54a3c93f6c4e68f55f3b93642c3c2f0d9f4919ad16e407ba3d4b279ef5b198c1cddbb744029f5a73f9e808e36f8f3f01a6989af9cec25b250d693220fad11d99a3e0e177fea317741419d22b3d27443a54099bbc299bb15b9e48fbc9bf95c6b8496bde67eaea3e8"),
        msg: "77d3f3e647e67766e5f4cf1bce5f631bd575ddbd02f29643a0c64dbd92191f2ae68db3dfadc3b62d0920873e87d13340af0ca3c5da99146a4492c8b76267fb477624192960f72e85b7ed9e8318fc1668be46c203539cc1470641d639def1600d4e228c8b098ac9b817e17cb329e8f5dd2aaaa23c160283220f5dde09aec134c2",
        mac: "724e5d2d51d98c15ce2e78f861d7b6f8952882e9d93d40850b78a23e632c4e14a222ab3726b1a0aa7c6b2cd66082ed95" },
    CavpHmacCase { l: 48, count: 286, klen: 145,
        key: concat!("95ece1c8ae5e", "94d16ec9983b1089a37395ad5b1d660916c13c87e4c13dbecf8f68c6611c324a679471def5487a93aaec86c935025b4518962884ac2cb04e66f7aa8e584b6860fb55b86c2b0a0873735dcd278bb525401f9ebaccd2beeac6830c26ebcf3c98c9d77d09194367014e872f306e641e0c21b241bc085e61354faf35a386cdd70aac83752d8d4449af4f6ccb78"),
        msg: "18dbab9f86b9d70bbdeb018f6a76ea7af23eb2ff111e9be3c13811795d8ae7d006c3e42b46547eb1f3c9e566565a435a8dbd42212e3fd0822d131f7300eaef4600c40f1d130521a388cb9ffe427f1bff19aacb9c7d0a44a15ce686a2469e3934d086365d36f449484498353d760cf9d15eac525a46a881a617584eed79cf4d03",
        mac: "2be1bd6a766e30792154cda00af97cc512e81413e0fb761698f39a26cecc3face6f9a98b7c49605126dfa5aa8de1ad72" },
    // ---- HMAC.rsp [L=64]  (HMAC-SHA-512), block size 128 B, untruncated Tlen=64 rows ----
    // Klen = 100 (< block size 128: zero-padded)
    CavpHmacCase { l: 64, count: 60, klen: 100,
        key: concat!("57c2eb677b50", "93b9e829ea4babb50bde55d0ad59fec34a618973802b2ad9b78e26b2045dda784df3ff90ae0f2cc51ce39cf54867320ac6f3ba2c6f0d72360480c96614ae66581f266c35fb79fd28774afd113fa5187eff9206d7cbe90dd8bf67c844e202"),
        msg: "2423dff48b312be864cb3490641f793d2b9fb68a7763b8e298c86f42245e4540eb01ae4d2d4500370b1886f23ca2cf9701704cad5bd21ba87b811daf7a854ea24a56565ced425b35e40e1acbebe03603e35dcf4a100e57218408a1d8dbcc3b99296cfea931efe3ebd8f719a6d9a15487b9ad67eafedf15559ca42445b0f9b42e",
        mac: "33c511e9bc2307c62758df61125a980ee64cefebd90931cb91c13742d4714c06de4003faf3c41c06aefc638ad47b21906e6b104816b72de6269e045a1f4429d4" },
    CavpHmacCase { l: 64, count: 61, klen: 100,
        key: concat!("7c98912c7442", "1362e112a2f98fed9babe0057fc778b4453239aaf5ac724b725553539770a5bc8666b8e13d0e9ce36b2b934c8137c7f20b5f391f41cefaeed92e9df8206cec3049bcda0c05deb9e6549fada19aa2618ff560f892ce6e4782aeff41cf53a9"),
        msg: "74e8936d83bf3f16b8d03fb73384ed8f46bd32343f5df8358107e2fdda293afa103a2bffbd4030e75d96cc7ca6ec7c97188fea88d4eb63b7b14e8b8c8dee4f8de12e1cc6981d4e6e223fecc7c491924632c7aef45fd8ef1494bcfb06c074616b0f4cce8abd5d83f32d550661357b18e5bcede841882c869251db9a331ac456dd",
        mac: "4cc28818486bb9b1b52e333dde71f73acc227488453fd907c6b51d349d67af1df29a9f225532ce04f50395fed565e98d78978626df93462d3f012f7373347298" },
    // Klen = 125 (< block size 128: zero-padded)
    CavpHmacCase { l: 64, count: 135, klen: 125,
        key: concat!("13fb1ed6389f", "32d1de3139cb04bcdd53525c9889b85379d3535a25d290351c95938a3d0cdaf38dbf1d5234bf7965c8ddce9ace1b66247e60d74ec7702a0f931a3cdf4cb465ca9fc458c380004a3a6e7957f1f813210b8038ba663fcdc42a8965d6a252b5224bf249552b2575bf64568db4091d58323006c3c34994d3a5"),
        msg: "88ad812fd34e55c809e817199604b4a7f7feae42cdc4c9e930db08e845a3d74313db8a57926706bf0551be758a0fe239f004d237c849d9e4bfac18292bf9c0c3e37985ea54b94f30d18c32ad2b53a059827cddb95a49b4bef1d369ead14eeeb4a18e592e40ca96e515a15908a05a57cd5570b611ab4ec23f7057e1725f29c9de",
        mac: "a481e713cdc81ca5afa0efcb16e35cd20d01aa449958fd2eaede2e25a5ba540beafba2fab4adfef2e146b4c1b2a1832e93dd373d63fa90bb61490f6568191f65" },
    CavpHmacCase { l: 64, count: 136, klen: 125,
        key: concat!("fd5070362296", "c40d65b105d5ab4653fe34e0200516933f3eeae03ed0c5d9f6016a8560b4bd86ab2f7bf98b22299ed3e54a394602d538aaf3e6951f2db4feaf5dc33426f15bb124da388d709083a28f5701ef96c28b3a3c75bef9332ef373b90771236af5e25d589504345d28a19ab0dbc1c9b74d1ee21c4bd8d423de6a"),
        msg: "8d2e68d7e9846cfa30d931a38efb59bcced53a14164b3163d2653888eeb0bb1448e1a80c65bcc6eb633447e72ed4a075f75d980fe2b19f35ffef62b27ce09c2019922faedb427321057fce19448d85962a08d1baddc936d1110e108e33d46f97e7882445b5df1ca4ff03edc237efaf264f1c0d9e705d9b3eee076ba57c56db82",
        mac: "b6cad1ca5ba505498a8f66a9422bf539426a8a55334fab9c6b9e08e3a5179d157d1efa0f91d5c5e26ffa43f5c1cb7ca5f906ce4f0efcf4e871820b8353e890e4" },
    // Klen = 128 (== block size 128: used verbatim)
    CavpHmacCase { l: 64, count: 210, klen: 128,
        key: concat!("e9e4480d1c4a", "621e0c4e1505992556347a7ab34fd2b289910474766cc969116f8040d96dc5f66cdc4454fa7bcfb9f838af19195038467ab8a16e1cbc12e598e6fd250e21b2145f1e2e859cf73400be12a0c69749f7100847429875351d5a76970b9ccf700c2ca3ad72e9e4c0f0840e8cf488158136989b0891f867211350134a"),
        msg: "b82eefb2081bd14dab0e9e345248a34ade73f3291886b91ea3e8cc742fd884f6ee0ccdaf4c9879f4db12dba58cf491af2541a1d5ef6cc8b1af750ef5d8559ef7ff9cd56d8f599974be3aecd8c0f4c08f3ae50d86f9f822a1e4ca39fd2f0b4d78d22630733a24d8d63ecdf9555411daf205a761c39ef46ff6292e74129bc13a7f",
        mac: "90093bdcc45da7338bd2efe92e30933b14f75582739c747f7572b3270b104f33af0c939e3c8ae53b2066fc8c97ccf38785cd2ec3d79e6946499d36121e44a3e7" },
    CavpHmacCase { l: 64, count: 211, klen: 128,
        key: concat!("d3fbd6fe4e35", "6ac1c8c120d432d7204d9d579b2a5a5d0c8b6016bd1eefd38dda735cf2f0ab873afe0a0916865e8b58a0af01fceb6a3765c9bfaceacc47a4916bea791afa003240d9b6563bebb3038949fc3aee38157dba596a9c4a20edccd187fff95904945d04b8925298e97b643ab24cab7af9a55890a2298de5022872d697"),
        msg: "b967c7d9c0a941f02e87723cf282eada4347b28193d3e0bfbeda6985886a37e646cc7b1cdbab45cce677528b3a0c24a08f8f580b779935c79398814d067298592a6bbff08248b5a2f0b48b0d28e4b6a2657763ac5ba00a8d6c86464b1eebe44ccd0c395e9dc9b9fbb306c6caa551c6682ec57869272e889ab26e6189b91f4248",
        mac: "bc9a83d782e50ba5a801146f8da39095d92387d759eb4ad52bbd9e99d9f68f4a0f6f6470c653c45979c2e19543804ced592ee9c53eb68a5b1b7746ed403ebe67" },
    // Klen = 139 (> block size 128: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 64, count: 285, klen: 139,
        key: concat!("95af10920dc7", "88269e70b8560b73135cf7f6f5b04a502c7bd61cb74f3b8ccd160701224922d865636a860d949ae755b970d3858c0ff37418a2d24b7142378ba11ab352e5c876da1a076642728b73916b2d24f8024876572363e7036510cec7f413ed28cec749ed33be3adf56a8bece597612d478bf84de85628367946df887f73dd92d6de7faa896d7276d"),
        msg: "61d91f317a902ea0944e11e92e6657a589e17abc027fcd869ff8b030e8870662f8a9e91ed3239cecfa42c0343d66cbebd1c2b771a25df7baea5cafad038424c97afb720e644e7d1bf5b829944ea2cec69766e68e4e580976de071c2274c0c5eb0e5421c9d51bba76ac39b3d009204680035771d9ad79eb02a3805d58e243cf0e",
        mac: "6e989ec9cbf010ad6691a672ff4ca90a00275f9ba4c81cd147cc506e1dbc8bc93b1d96a375e493503c0ac697f7c45e4fadf138242df7e06e677de245afa97780" },
    CavpHmacCase { l: 64, count: 286, klen: 139,
        key: concat!("27e6c9f270b9", "855c9658ad0e3d6c9a111a624f66fa64a49a0688a49b454733ca6230f451b0dd69b76b275cb241967e3c101b4fe8f2023d77772210a63157854b763239a061eec9df1aa6380f57c6911d23c0cd2edf00f63486218dbf35612a17ea5262878bd3edfb2b3f08ce8ae419dddab792e0c94517fabbede38e574d685546fa35ad37741d34275996"),
        msg: "df24279bf8277ad1091972b82594d84677e54fe5d65786d19ab5b2c1ae0a3cc9e7abb67f9477145d575e196633200f0ce557bb5278b8902e1496233117a7df69660bfa87068aa73de61e8eeaffb179799f275086029f47c323f6569bd18dea15054ddafa73e89c3a5f61b98cb2ce7e554d5df4cb9d95135a70de33470744c393",
        mac: "e6f6061275a89345f5463cfa198d528e14047d478f69ad7a73432f18f88bc68a1b8aba2c3b025c93b25deb8f403763a55024408a97a903e95f0cb6178e7be389" },
    // Klen = 142 (> block size 128: HASHED first (FIPS 198-1 step 2))
    CavpHmacCase { l: 64, count: 360, klen: 142,
        key: concat!("01b95a887927", "ce31b1242391bbd00965eb77a903d4b8399b72e6cebda9ae721beefa779145160b626b110cc554671da0d8dcf993a9ab073888e02fa9b803ed43b3f6a3aa1d20340df6ccceac13cb0797cf612cb8fe5fd513228cbd4de249d16bb77587dde98f71bbba1a124ee046f0d239ccea7abb1accb5aab021b00dca491c623fcb3191a9ecf31fc680b4a41e"),
        msg: "632afa8e79b14b2a3604f5855d2bf182d3c56d6853f21fe46271da5286065f38b31f751306b63c57b679beb14729c78f0040f7e2a0d615224dc5a693cd0cbec8f87117656d6b6029853ed72b85681a63183c3a6dfccd128afb0dd7e81d36f0231c69070b189560a88c9b697b81b0930701026190cf9ebe23559194d6de4d9a51",
        mac: "210ad45ca2fd1f105c0a18f993774f933ece57ace4da619689e1cb8b491a189cc6e4ee1954a32201072e70f934837c0fb6e239b4fdfbd26ebf11b9a919eafd09" },
    CavpHmacCase { l: 64, count: 361, klen: 142,
        key: concat!("61096f4fe534", "0488916de293be38cc3ae0c877670c713637b760d74fc18ac773b2e27d5543cf16aa20dd3d83ecb34edb8545bb6c8a4aaec81bf1f0a4e0cf09774d1ca944242046b33be807677f3de18c39d700af90cd68d34f50dcc1e999fe9fbb20b9c4900fdccb6af607e680c0cb7583e60dd825e2ab81dce7634de3cff0148355757f90841f19366f06a9f623"),
        msg: "67e704046f98cb5aa97da95b19147391f05788f811366b0ece44b12af2b11e0e05780bbfcbd90a950e0acd8e9d2a44e7957606eedfbff212fa1c163cfbdcd062d2be3259ce65abea6406e4292c64e9022cfe89155986ffc45b96d289919ff98d552243778122f68231d9b6d3cbaaa9093d57d9158674da4c781bacbabce2e2ba",
        mac: "9a2d147e50827157f3866e868c1cca9f081579c92f25da8cebc9ed249928c82bead39d480ecbb5b5d0e0755029aebf3e0206984f3ea83f4d6372f4453390e070" },
];

#[test]
fn cavp_hmac_vectors() {
    for c in CAVP_HMAC {
        let key = unhex(c.key);
        let msg = unhex(c.msg);
        assert_eq!(key.len(), c.klen, "CAVP row [L={}] Count={}: Klen disagrees", c.l, c.count);
        let computed = match c.l {
            28 => tag::<Sha224>(&key, &msg),
            32 => tag::<Sha256>(&key, &msg),
            48 => tag::<Sha384>(&key, &msg),
            64 => tag::<Sha512>(&key, &msg),
            other => panic!("no digest of output size {other}"),
        };
        assert_eq!(
            computed,
            c.mac,
            "HMAC-SHA-{} disagrees with NIST CAVP HMAC.rsp [L={}] Count = {} (Klen = {})",
            c.l * 8,
            c.l,
            c.count,
            c.klen
        );
    }
}

/// The published rows must span all three key branches at BOTH block sizes.
///
/// This is the guard for the classic HMAC bug: deciding "is the key too long?"
/// against the *output* size instead of the *block* size. RFC 4231 alone cannot
/// see it — its long-key cases use a 131-byte key, which exceeds 32, 64 and 128
/// alike, so both rules agree. A `Klen` of exactly 64 (SHA-256) or exactly 128
/// (SHA-512), and one just above, is what distinguishes them.
#[test]
fn cavp_hmac_covers_the_key_length_boundaries() {
    for (l, block) in [(28usize, 64usize), (32, 64), (48, 128), (64, 128)] {
        let klens: Vec<usize> = CAVP_HMAC.iter().filter(|c| c.l == l).map(|c| c.klen).collect();
        assert!(!klens.is_empty(), "no CAVP rows for L={l}");
        assert!(
            klens.iter().any(|&k| k < block),
            "L={l}: no key shorter than the {block}-byte block"
        );
        assert!(
            klens.iter().any(|&k| k == block),
            "L={l}: no key EXACTLY the {block}-byte block — the used-verbatim branch is untested"
        );
        assert!(
            klens.iter().any(|&k| k > block),
            "L={l}: no key longer than the {block}-byte block"
        );
    }
}

// ===========================================================================
// Tier D — DERIVED: repeated-byte messages at the padding boundaries
// ===========================================================================
//
// PROVENANCE: NOT published. `key = [0x5a; 32]` (the key size both consumers in
// this tree use), `msg = [0xa5; n]`. Expected values from CPython `hmac`
// (OpenSSL); re-derived from the incumbent `hmac` crate by the test below.

/// The key every tier-D row uses. 32 bytes, matching `trust-cache` and
/// `trust-buildcache`, and shorter than both block sizes so the zero-padding
/// branch is the one under test.
const DERIVED_KEY: [u8; 32] = [0x5a; 32];

/// The repeated message byte.
const DERIVED_FILL: u8 = 0xa5;

/// `(message length, expected HMAC-SHA-256)` — DERIVED, not published.
///
/// 55/56 and 119/120 are the inner hash's FIPS 180-4 §5.1.1 transitions;
/// 63/64 and 127/128 the block fill and exact block.
#[rustfmt::skip]
const DERIVED_HMAC_SHA256: &[(usize, &str)] = &[
    (0, "87a26610b4e32f22d6d403b2397f534fb64c83b15aa53deaec60b1afa31dbb74"),
    (54, "b15868c31fd3b8bd9ba5ca63f13ebadacf89e1862ca7766cf76a6dfb596f5e5a"),
    (55, "7146972f7e6d59331d178e5f75918ffe606fb63d6296e8549b46b2557b793dc4"),
    (56, "b57f30615d3b91403338da020ca3364cc2a4d290110700199c52244dbcdb4238"),
    (57, "41737232f2c945ae326252473cf0ceac70db64db84e2d447b1837ebefa087b7b"),
    (63, "bb60b2c3a8c6476e5e81d7cd4014ca30ca32bf6e5eda9b88b206ddaefc17f5fd"),
    (64, "948e9695d280c992071c902b2817ee8ad2ac1e70476630d54b2ce257a03c13c7"),
    (65, "1c3caf971ea0bdfda57947621c0e391942980038412e2b87c16a8b0d43d6caff"),
    (118, "40028294a5f086145f18b9e3b39cd3732d303c1de0699becd7b93ca831a3412e"),
    (119, "64ffca12cac74c7dd0452b55d3689182c92f2ac770dbfadc5f47e717886ff7c2"),
    (120, "42c9c6fef71de3f87bbdbb4402bfb9c5676b912252f1c9bcc3158a84546a6f97"),
    (127, "51077df28774123b702debc6b40cde9db47c3435387d25b83c3b4442d1babb07"),
    (128, "30a152d2248718d523fdda1e810dd647fbffd6509da0fed2522dc7344942f0f7"),
    (129, "d621a7d0453fcb567eb3f0e9f8aa894d10a7ffd4c335775afcdf120b503d2c5f"),
];

/// `(message length, expected HMAC-SHA-512)` — DERIVED, not published.
///
/// 111/112 and 239/240 are the inner hash's FIPS 180-4 §5.1.2 transitions;
/// 127/128 the block fill and exact block.
#[rustfmt::skip]
const DERIVED_HMAC_SHA512: &[(usize, &str)] = &[
    (0, "e1c6c7d1bbc2aa877fa338ae6784f77ea537e8c86f289487404fdbf12a45f80454e965ec6a2ce1e4f79963a9411fa6f676b4db4008e836aa11075e094cc27d60"),
    (110, "c7ec00702f43ccdc826b2492c13a62f2f6899067025db1c36191c95ccc4134c92b75ff4ff8492049cabc9e2bab40ce3f550fa866a7f0ef0a28ac91bb6deac5de"),
    (111, "47084a64116b67a0dba3f503649d1d0d2377f6f02c9890e659038ac19f55087203ccb179dc7188673a48bf06c7b6c351d224d513d7e749237a86a66a45c1ed3f"),
    (112, "17f0134c26e3d739df3b7cea164a27e4480dfe4a296bc930861e6e3e06a2eaa4c281ae2f439bb5d424815fe3e496174a75867cf2b2880d1bd75ef4128955dd1d"),
    (113, "3f1090c9b9f207c25c3c70a40a5197eecd2e956c298bfdd849d19babf8a9b2f67632a0008d07496ace3ced48f4de11c756980f2ca1fc5029857f8054ec1e9f81"),
    (118, "3d8ac8f67d71051af78a5f7fc714df8ad8b3a8cc9c88073ad9ab184243fd834b452767040f39d714ae324c3ee60a905c117cc8c89f2b045884fe7ac97338f776"),
    (119, "fc84ce7268f68fb3f7168fdd1c9d71cca15670a904ccaf301ad74ff8b08b1028b5ec65c119f755836a4143dd94e80a4efe941a6962b1848b43f60379682688b3"),
    (120, "814069aac6341608a0c30bb2d121155e7e6474aef7716ad6c5d7be1ee29571b30848825804fe62e0ff3e897e8f44f783ad3b393c69c37f5a8c91a407d83ed82c"),
    (126, "f5f55402d2e20ce0f65725d31535ddb86dfcf7822d839168e7456c12a953b3e74571e1c2a7ba734d9448cce16e5f0d092ef6aea41dca919ec3465783b5790115"),
    (127, "5ea46e68c37e817f4021421c2e56a416b8e1fab3d477a0bb92d98fece155eddbaee1daf7695fa4d913286489659c5e12d06ed3028aba356c49f6703907c12e86"),
    (128, "e6c708f472418b35f90cfb0f8a1d8c762046b9083c086d824dfa7d06abe8ceb1b7571acd68f92771fd92c13a55e690d1dff6ef3782ad35a61e0cabf093117922"),
    (129, "90ad5f3811e339d9dcba8d3fbad691c42ec0f363e416bbfa4b73a90a3f57d245105b532e8c21d8b58c366fe1f4943cf8aff540eec8e1c515de47f7accfda3fe4"),
    (239, "e606214c5ca38f309802f87ed100d21e333230af87e042673a4c38b6e3d93b019c20dcadd2bfc33de7ff1bcbd0a5655dab23ab3f734f8dd1544bf843941f2e61"),
    (240, "fae8f3984404d970572d46c3a9f38500085dffe9f9f5cbadeebe419b4a0291d1a42381a88254c7015bb823446dec12519ceb9f39b00276aeb72b479301d744a1"),
];

#[test]
fn derived_repeated_byte_message_boundaries_sha256() {
    for &(len, expected) in DERIVED_HMAC_SHA256 {
        let message = vec![DERIVED_FILL; len];
        assert_eq!(
            tag::<Sha256>(&DERIVED_KEY, &message),
            expected,
            "HMAC-SHA-256 disagrees on a {len}-byte message"
        );
    }
}

#[test]
fn derived_repeated_byte_message_boundaries_sha512() {
    for &(len, expected) in DERIVED_HMAC_SHA512 {
        let message = vec![DERIVED_FILL; len];
        assert_eq!(
            tag::<Sha512>(&DERIVED_KEY, &message),
            expected,
            "HMAC-SHA-512 disagrees on a {len}-byte message"
        );
    }
}

/// The DERIVED label, enforced against the incumbent on every run.
///
/// **Delete this test with the `hmac`/`sha2` dev-dependencies** when the
/// incumbent leaves the graph; the tables above survive and keep their OpenSSL
/// provenance.
#[test]
fn derived_rows_are_reproduced_by_the_incumbent_hmac_crate() {
    use hmac::Mac as IncumbentMac;

    for &(len, expected) in DERIVED_HMAC_SHA256 {
        let mut mac = <hmac::Hmac<sha2::Sha256> as IncumbentMac>::new_from_slice(&DERIVED_KEY)
            .expect("any key length");
        mac.update(&vec![DERIVED_FILL; len]);
        assert_eq!(
            hex(&mac.finalize().into_bytes()),
            expected,
            "the DERIVED HMAC-SHA-256 row for {len} bytes is not what the incumbent computes"
        );
    }
    for &(len, expected) in DERIVED_HMAC_SHA512 {
        let mut mac = <hmac::Hmac<sha2::Sha512> as IncumbentMac>::new_from_slice(&DERIVED_KEY)
            .expect("any key length");
        mac.update(&vec![DERIVED_FILL; len]);
        assert_eq!(
            hex(&mac.finalize().into_bytes()),
            expected,
            "the DERIVED HMAC-SHA-512 row for {len} bytes is not what the incumbent computes"
        );
    }
}

/// The brief names these lengths; a table cannot lose them silently.
#[test]
fn derived_tables_cover_the_required_message_lengths() {
    for &want in &[0usize, 55, 56, 63, 64] {
        assert!(
            DERIVED_HMAC_SHA256.iter().any(|&(n, _)| n == want),
            "DERIVED_HMAC_SHA256 lost the {want}-byte row"
        );
    }
    for &want in &[0usize, 111, 112, 127, 128] {
        assert!(
            DERIVED_HMAC_SHA512.iter().any(|&(n, _)| n == want),
            "DERIVED_HMAC_SHA512 lost the {want}-byte row"
        );
    }
}

// ===========================================================================
// The published tags must also VERIFY, not merely compare equal
// ===========================================================================

/// `verify_slice` is the half of the surface a KAT normally never touches: the
/// tests above all go through `finalize`. A MAC whose comparison is broken but
/// whose computation is right passes every vector in this file.
#[test]
fn published_tags_verify_and_near_misses_do_not() {
    for c in RFC4231 {
        // Case 5 is published truncated and this crate exposes no truncated
        // verifier, so it has no full-length tag to verify against.
        if c.sha256.len() != 2 * Sha256::OUTPUT_SIZE {
            continue;
        }
        let key = unhex(c.key);
        let data = unhex(c.data);
        let expected = unhex(c.sha256);

        let mut mac = Hmac::<Sha256>::new_from_slice(&key).expect("any key length");
        mac.update(&data);
        assert!(mac.verify_slice(&expected).is_ok(), "case {}: the RFC tag must verify", c.case);

        // One flipped bit in the first and last byte must be rejected.
        for index in [0usize, expected.len() - 1] {
            let mut corrupted = expected.clone();
            corrupted[index] ^= 0x01;
            let mut mac = Hmac::<Sha256>::new_from_slice(&key).expect("any key length");
            mac.update(&data);
            assert!(
                mac.verify_slice(&corrupted).is_err(),
                "case {}: a corrupted tag must not verify",
                c.case
            );
        }
    }
}
