// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Malformed input must return `Err`, never panic.
//!
//! The requirement is specific: no index-out-of-bounds, no slicing panic, no
//! `unwrap`/`expect` on parsed data, no unbounded allocation driven by an
//! attacker-supplied length. A panic inside a `#[test]` is a test failure, so
//! every case below is simultaneously a panic assertion and an outcome
//! assertion.
//!
//! WHAT THIS DOES NOT CLAIM. It is not proof of total absence of panics; it is
//! a systematic sweep over the shapes that reach every decode path. And it
//! deliberately does NOT test unbounded RECURSION: like the incumbent, this
//! crate has no depth limit, so a sufficiently nested hostile input overflows
//! the stack and aborts. That is a documented inherited divergence (see
//! `lib.rs`), not something this file hides — the bounded-depth case below
//! pins the behaviour that IS defined.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_bincode::{DefaultOptions, Options};

#[derive(Serialize, Deserialize, Debug, PartialEq)]
struct S {
    a: u8,
    b: String,
    c: Vec<u32>,
    d: Option<Box<S>>,
    e: E,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
enum E {
    A,
    B(u64),
    C { x: char, y: f64 },
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
enum Nest {
    Leaf(u8),
    Node(Box<Nest>),
}

/// A deterministic xorshift, so a failure is always reproducible from the seed
/// printed in the assertion message. No `rand` dependency, by design.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn byte(&mut self) -> u8 {
        (self.next_u64() >> 24) as u8
    }
}

/// Runs one input through every decode lane for one type. Returning at all is
/// the assertion: a panic here fails the test.
macro_rules! all_lanes {
    ($ty:ty, $bytes:expr) => {{
        let b: &[u8] = $bytes;
        let _ = trust_bincode::deserialize::<$ty>(b);
        let _ = trust_bincode::deserialize_from::<&[u8], $ty>(b);
        let _ = DefaultOptions::new().deserialize::<$ty>(b);
        let _ = DefaultOptions::new().deserialize_from::<&[u8], $ty>(b);
        let _ = DefaultOptions::new()
            .with_fixint_encoding()
            .with_big_endian()
            .reject_trailing_bytes()
            .deserialize::<$ty>(b);
        let _ = DefaultOptions::new()
            .with_fixint_encoding()
            .reject_trailing_bytes()
            .with_limit(64)
            .deserialize_from::<&[u8], $ty>(b);
    }};
}

macro_rules! all_types {
    ($bytes:expr) => {{
        all_lanes!(u8, $bytes);
        all_lanes!(i8, $bytes);
        all_lanes!(u16, $bytes);
        all_lanes!(i16, $bytes);
        all_lanes!(u32, $bytes);
        all_lanes!(i32, $bytes);
        all_lanes!(u64, $bytes);
        all_lanes!(i64, $bytes);
        all_lanes!(u128, $bytes);
        all_lanes!(i128, $bytes);
        all_lanes!(f32, $bytes);
        all_lanes!(f64, $bytes);
        all_lanes!(bool, $bytes);
        all_lanes!(char, $bytes);
        all_lanes!(String, $bytes);
        all_lanes!(Vec<u8>, $bytes);
        all_lanes!(Vec<String>, $bytes);
        all_lanes!(BTreeMap<u8, String>, $bytes);
        all_lanes!(Option<u32>, $bytes);
        all_lanes!((u8, u32, String), $bytes);
        all_lanes!([u8; 4], $bytes);
        all_lanes!(E, $bytes);
        all_lanes!(S, $bytes);
    }};
}

#[test]
fn every_single_byte_input_is_handled_without_panicking() {
    for b in 0u8..=255 {
        all_types!(&[b]);
    }
}

#[test]
fn empty_input_is_handled_without_panicking() {
    all_types!(&[]);
}

#[test]
fn pseudorandom_garbage_is_handled_without_panicking() {
    let mut rng = Rng(0x2026_08_25_bc01);
    for len in [0usize, 1, 2, 3, 4, 7, 8, 9, 16, 17, 33, 64, 129] {
        for _ in 0..40 {
            let input: Vec<u8> = (0..len).map(|_| rng.byte()).collect();
            all_types!(&input);
        }
    }
}

#[test]
fn every_truncation_of_a_valid_encoding_is_handled_without_panicking() {
    let value = S {
        a: 7,
        b: "héllo 𝄞".to_string(),
        c: vec![1, 70000, u32::MAX],
        d: Some(Box::new(S {
            a: 1,
            b: String::new(),
            c: vec![],
            d: None,
            e: E::A,
        })),
        e: E::C {
            x: '𝄞',
            y: f64::NEG_INFINITY,
        },
    };
    for cfg_bytes in [
        trust_bincode::serialize(&value).unwrap(),
        DefaultOptions::new().serialize(&value).unwrap(),
    ] {
        for cut in 0..cfg_bytes.len() {
            all_types!(&cfg_bytes[..cut]);
        }
        // ...and every one-byte corruption at every position.
        for pos in 0..cfg_bytes.len() {
            for delta in [1u8, 0x7f, 0xff] {
                let mut bad = cfg_bytes.clone();
                bad[pos] = bad[pos].wrapping_add(delta);
                all_types!(&bad);
            }
        }
    }
}

#[test]
fn a_hostile_length_prefix_never_drives_an_unbounded_allocation() {
    // The classic amplification attack: a tiny input whose length prefix says
    // "now allocate 18 exabytes". Both paths must return Err promptly.
    //
    // NOTE the lanes are split by encoding on purpose. The same bytes are not
    // hostile under both: `00 00 00 00 00 00 00 01` is 2^56 under fixint but
    // an empty sequence plus trailing junk under varint, and the reader path
    // ACCEPTS that (it never applies the trailing-bytes check). Asserting
    // `is_err()` for every lane would be asserting the wrong thing, and would
    // be "fixed" later by weakening the test.
    let fixint_hostile: [&[u8]; 3] = [
        &[0xff; 8],                                        // len = u64::MAX
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f], // i64::MAX
        &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01], // 2^56
    ];
    let varint_hostile: [&[u8]; 3] = [
        &[0xfd, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff], // u64::MAX
        &[0xfd, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f], // i64::MAX
        &[0xfc, 0xff, 0xff, 0xff, 0xff],                         // u32::MAX
    ];

    for input in fixint_hostile {
        for lane in 0..2 {
            let r: Result<Vec<u8>, _> = if lane == 0 {
                trust_bincode::deserialize(input)
            } else {
                trust_bincode::deserialize_from(input)
            };
            assert!(
                r.is_err(),
                "fixint hostile length {input:02x?} lane {lane} decoded successfully"
            );
            let r: Result<String, _> = if lane == 0 {
                trust_bincode::deserialize(input)
            } else {
                trust_bincode::deserialize_from(input)
            };
            assert!(r.is_err(), "fixint hostile {input:02x?} lane {lane} String");
        }
    }

    for input in varint_hostile {
        for lane in 0..2 {
            let r: Result<Vec<u8>, _> = if lane == 0 {
                DefaultOptions::new().deserialize(input)
            } else {
                DefaultOptions::new().deserialize_from(input)
            };
            assert!(
                r.is_err(),
                "varint hostile length {input:02x?} lane {lane} decoded successfully"
            );
            let r: Result<String, _> = if lane == 0 {
                DefaultOptions::new().deserialize(input)
            } else {
                DefaultOptions::new().deserialize_from(input)
            };
            assert!(r.is_err(), "varint hostile {input:02x?} lane {lane} String");
        }
    }
}

#[test]
fn the_reader_path_rejects_a_u64_max_length_rather_than_aborting() {
    // THIS IS THE ONE DELIBERATE IMPLEMENTATION DIVERGENCE from the incumbent,
    // pinned so it cannot be "simplified" back.
    //
    // bincode 1.3.3's `IoReader::fill_buffer` does `temp_buffer.resize(length,
    // 0)` and would attempt an 18-exabyte allocation here. The capture agent
    // had to SKIP the reader lanes of the `vec_u8_len_u64_max` fixture case
    // for exactly that reason (`reader_lanes_run_for_unlimited_configs:
    // false`), so no incumbent observation exists to compare against — this is
    // the only place the behaviour is stated.
    let input: &[u8] = &[0xff; 8];
    let err = trust_bincode::deserialize_from::<&[u8], Vec<u8>>(input).unwrap_err();
    assert_eq!(err.to_string(), "io error: failed to fill whole buffer");

    let input: &[u8] = &[0xfd, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
    let err = DefaultOptions::new()
        .deserialize_from::<&[u8], Vec<u8>>(input)
        .unwrap_err();
    assert_eq!(err.to_string(), "io error: failed to fill whole buffer");
}

#[test]
fn bounded_deep_nesting_still_round_trips() {
    // The fixture's subprocess probe recorded depths 1000/5000/10000/20000 as
    // ACCEPT and 50000+ as killed by SIGABRT (stack overflow). This pins a
    // depth well inside the accepting range; the aborting range is NOT tested,
    // because the incumbent aborts there too and a test cannot survive it.
    let mut n = Nest::Leaf(7);
    for _ in 0..500 {
        n = Nest::Node(Box::new(n));
    }
    let bytes = DefaultOptions::new().serialize(&n).unwrap();
    assert_eq!(bytes.len(), 502); // 500 varint `01` + `00` + payload
    let back: Nest = DefaultOptions::new().deserialize(&bytes).unwrap();
    assert_eq!(back, n);
}

#[test]
fn a_truncated_utf8_payload_errors_rather_than_producing_a_bad_string() {
    // Length says 4, only the first two bytes of a 4-byte scalar follow.
    let input: &[u8] = &[4, 0, 0, 0, 0, 0, 0, 0, 0xf0, 0x9d];
    assert!(trust_bincode::deserialize::<String>(input).is_err());
    assert!(trust_bincode::deserialize::<&str>(input).is_err());

    // Length 4, four bytes that are not valid UTF-8.
    let input: &[u8] = &[4, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xfe, 0xfd, 0xfc];
    let err = trust_bincode::deserialize::<String>(input).unwrap_err();
    assert!(
        err.to_string().starts_with("string is not valid utf8:"),
        "unexpected message: {err}"
    );
}

#[test]
fn map_and_seq_length_lies_error_rather_than_looping_forever() {
    // Says 3 entries, supplies one.
    let input: &[u8] = &[3, 0, 0, 0, 0, 0, 0, 0, 1, 2];
    assert!(trust_bincode::deserialize::<BTreeMap<u8, u8>>(input).is_err());
    // Says 3 elements of a variable-length type, supplies none.
    let input: &[u8] = &[3, 0, 0, 0, 0, 0, 0, 0];
    assert!(trust_bincode::deserialize::<Vec<String>>(input).is_err());
}
