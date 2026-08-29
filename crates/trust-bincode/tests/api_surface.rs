// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The parts of the drop-in surface the golden fixture does not reach.
//!
//! The fixture pins bytes and messages for the four configurations the capture
//! used. What it does NOT cover, and what is therefore covered here, is called
//! out case by case below. Where a case is un-pinned by any incumbent
//! observation — big/native endian, `deserialize_identifier`,
//! `deserialize_ignored_any`, `deserialize_in_place`, the `*_seed` API — the
//! test says so, because "we agree with ourselves" is weaker evidence than
//! "we agree with the incumbent" and the difference must stay visible.

use std::collections::BTreeMap;

use serde::de::{IgnoredAny, Visitor};
use serde::{Deserialize, Serialize};
use trust_bincode::{DefaultOptions, ErrorKind, Options};

// ---------------------------------------------------------------------------
// THE DEFAULTS TRAP — the single most consequential thing to get right
// ---------------------------------------------------------------------------

#[test]
fn free_functions_are_fixint_allow_trailing_and_the_struct_is_varint_reject() {
    // Fixint: 251u32 is four literal bytes.
    assert_eq!(trust_bincode::serialize(&251u32).unwrap(), vec![
        0xfb, 0, 0, 0
    ]);
    // Varint: 251 is above the 250 single-byte ceiling, so marker + u16 LE.
    assert_eq!(DefaultOptions::new().serialize(&251u32).unwrap(), vec![
        0xfb, 0xfb, 0x00
    ]);

    // Trailing: allowed by the free function, rejected by the struct.
    let with_junk = [1u8, 0, 0, 0, 0x41];
    assert_eq!(trust_bincode::deserialize::<u32>(&with_junk).unwrap(), 1);
    let err = DefaultOptions::new()
        .with_fixint_encoding()
        .deserialize::<u32>(&with_junk)
        .unwrap_err();
    assert_eq!(err.to_string(), "Slice had bytes remaining after deserialization");

    // `options()` is `DefaultOptions::new()`.
    assert_eq!(
        trust_bincode::options().serialize(&251u32).unwrap(),
        DefaultOptions::new().serialize(&251u32).unwrap()
    );
}

// ---------------------------------------------------------------------------
// The limit, in all three positions
// ---------------------------------------------------------------------------

#[test]
fn limit_is_enforced_on_serialize_and_on_reader_decode_but_not_on_slice_decode() {
    let cfg = || DefaultOptions::new().with_fixint_encoding().with_limit(16);

    // Serialize: enforced, via the serialized_size pre-pass.
    let err = cfg().serialize(&vec![0u8; 100]).unwrap_err();
    assert_eq!(err.to_string(), "the size limit has been reached");
    assert!(matches!(*err, ErrorKind::SizeLimit));

    // A 28-byte encoding of a 20-byte string.
    let payload = trust_bincode::serialize(&"a".repeat(20)).unwrap();
    assert_eq!(payload.len(), 28);

    // Slice decode: NOT enforced. This is the incumbent's behaviour and
    // `first-party/trust-ir` depends on it; see config's module docs.
    assert_eq!(cfg().deserialize::<String>(&payload).unwrap(), "a".repeat(20));

    // Reader decode: enforced.
    let err = cfg().deserialize_from::<&[u8], String>(&payload[..]).unwrap_err();
    assert_eq!(err.to_string(), "the size limit has been reached");

    // with_no_limit undoes it.
    assert_eq!(
        cfg()
            .with_no_limit()
            .deserialize_from::<&[u8], String>(&payload[..])
            .unwrap(),
        "a".repeat(20)
    );
}

#[test]
fn a_failed_serialize_into_writes_nothing() {
    let mut sink: Vec<u8> = Vec::new();
    let err = DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(4)
        .serialize_into(&mut sink, &vec![0u8; 100])
        .unwrap_err();
    assert_eq!(err.to_string(), "the size limit has been reached");
    assert!(sink.is_empty(), "bytes leaked into the writer before the refusal");
}

// ---------------------------------------------------------------------------
// The free-function reader/writer lanes
// ---------------------------------------------------------------------------

#[test]
fn serialize_into_and_deserialize_from_round_trip() {
    let value = (1u8, "x".to_string(), true);
    let mut buf: Vec<u8> = Vec::new();
    trust_bincode::serialize_into(&mut buf, &value).unwrap();
    // NOTE: `serialize_into` is fixint but does NOT set allow_trailing — that
    // only matters on decode, so the bytes equal `serialize`'s.
    assert_eq!(buf, trust_bincode::serialize(&value).unwrap());

    let back: (u8, String, bool) = trust_bincode::deserialize_from(&buf[..]).unwrap();
    assert_eq!(back, value);
    assert_eq!(
        trust_bincode::serialized_size(&value).unwrap(),
        buf.len() as u64
    );
}

#[test]
fn deserialize_in_place_reuses_the_destination() {
    // UN-PINNED by the fixture: the capture did not exercise
    // `deserialize_in_place`. Self-consistency only.
    //
    // NOTE the reachability quirk, which is the incumbent's: the free
    // `deserialize_in_place` and `Options::deserialize_in_place` both take a
    // `BincodeRead`, and the two implementations of that trait have
    // crate-private constructors. So the only externally reachable spelling is
    // through `Deserializer::from_slice`, which is what a consumer would have
    // to write against the incumbent too.
    let bytes = trust_bincode::serialize(&vec![7u8, 8, 9]).unwrap();

    let mut place: Vec<u8> = vec![1, 2, 3, 4, 5];
    let de = trust_bincode::Deserializer::from_slice(
        &bytes,
        DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes(),
    );
    let mut de = de;
    serde::Deserialize::deserialize_in_place(&mut de, &mut place).unwrap();
    assert_eq!(place, vec![7, 8, 9]);
}

#[test]
fn deserialize_seed_and_from_seed_are_reachable() {
    // UN-PINNED by the fixture. Self-consistency only.
    let bytes = trust_bincode::serialize(&42u32).unwrap();
    let cfg = || {
        DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
    };
    let v: u32 = cfg()
        .deserialize_seed(std::marker::PhantomData::<u32>, &bytes)
        .unwrap();
    assert_eq!(v, 42);
    let v: u32 = cfg()
        .deserialize_from_seed(std::marker::PhantomData::<u32>, &bytes[..])
        .unwrap();
    assert_eq!(v, 42);
}

// ---------------------------------------------------------------------------
// Endianness — no incumbent observation exists for these
// ---------------------------------------------------------------------------

#[test]
fn big_endian_and_native_endian_are_available_and_self_consistent() {
    // UN-PINNED by the fixture: the capture recorded little-endian only,
    // because no caller in this tree uses anything else. These assertions are
    // derived from the format definition, not from the incumbent.
    let be = DefaultOptions::new()
        .with_fixint_encoding()
        .with_big_endian()
        .serialize(&0x1234_5678u32)
        .unwrap();
    assert_eq!(be, vec![0x12, 0x34, 0x56, 0x78]);

    let le = DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .serialize(&0x1234_5678u32)
        .unwrap();
    assert_eq!(le, vec![0x78, 0x56, 0x34, 0x12]);

    let ne = DefaultOptions::new()
        .with_fixint_encoding()
        .with_native_endian()
        .serialize(&0x1234_5678u32)
        .unwrap();
    assert_eq!(ne, if cfg!(target_endian = "little") { le } else { be });

    // Round trip under big-endian, including a varint payload, whose trailing
    // u16 must also follow the configured order.
    let cfg = || {
        DefaultOptions::new()
            .with_big_endian()
            .reject_trailing_bytes()
    };
    let bytes = cfg().serialize(&300u32).unwrap();
    assert_eq!(bytes, vec![0xfb, 0x01, 0x2c]);
    assert_eq!(cfg().deserialize::<u32>(&bytes).unwrap(), 300);
}

// ---------------------------------------------------------------------------
// The refusals
// ---------------------------------------------------------------------------

#[test]
fn deserialize_any_is_a_refusal_with_the_incumbents_text() {
    #[derive(Debug)]
    struct AnyProbe;
    impl<'de> Deserialize<'de> for AnyProbe {
        fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            struct V;
            impl<'de> Visitor<'de> for V {
                type Value = AnyProbe;
                fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.write_str("anything")
                }
            }
            d.deserialize_any(V)
        }
    }
    let err = trust_bincode::deserialize::<AnyProbe>(&[0]).unwrap_err();
    assert_eq!(
        err.to_string(),
        "Bincode does not support the serde::Deserializer::deserialize_any method"
    );
    assert!(matches!(*err, ErrorKind::DeserializeAnyNotSupported));
}

#[test]
fn deserialize_identifier_and_ignored_any_are_refusals() {
    // UN-PINNED by the fixture: the capture could not reach these through
    // ordinary derived types, because `deserialize_struct` delegates to
    // `deserialize_tuple`. They are driven directly here.
    #[derive(Debug)]
    struct IdentProbe;
    impl<'de> Deserialize<'de> for IdentProbe {
        fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            struct V;
            impl<'de> Visitor<'de> for V {
                type Value = IdentProbe;
                fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.write_str("an identifier")
                }
            }
            d.deserialize_identifier(V)
        }
    }
    let err = trust_bincode::deserialize::<IdentProbe>(&[0]).unwrap_err();
    assert_eq!(
        err.to_string(),
        "Bincode does not support Deserializer::deserialize_identifier"
    );
    assert!(matches!(*err, ErrorKind::Custom(_)));

    let err = trust_bincode::deserialize::<IgnoredAny>(&[0]).unwrap_err();
    assert_eq!(
        err.to_string(),
        "Bincode does not support Deserializer::deserialize_ignored_any"
    );

    // And the write-side refusal, which the fixture DOES pin.
    struct UnknownLen;
    impl Serialize for UnknownLen {
        fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            use serde::ser::SerializeSeq;
            let mut seq = s.serialize_seq(None)?;
            seq.serialize_element(&1u8)?;
            seq.end()
        }
    }
    let err = trust_bincode::serialize(&UnknownLen).unwrap_err();
    assert_eq!(
        err.to_string(),
        "Bincode can only encode sequences and maps that have a knowable size ahead of time"
    );
    assert!(matches!(*err, ErrorKind::SequenceMustHaveLength));
}

// ---------------------------------------------------------------------------
// Byte and borrowed-string paths
// ---------------------------------------------------------------------------

#[test]
fn bytes_and_byte_buf_paths_round_trip_and_match_vec_u8() {
    struct Bytes<'a>(&'a [u8]);
    impl Serialize for Bytes<'_> {
        fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            s.serialize_bytes(self.0)
        }
    }
    #[derive(Debug, PartialEq)]
    struct ByteBuf(Vec<u8>);
    impl<'de> Deserialize<'de> for ByteBuf {
        fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            struct V;
            impl<'de> Visitor<'de> for V {
                type Value = ByteBuf;
                fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.write_str("bytes")
                }
                fn visit_bytes<E>(self, v: &[u8]) -> Result<ByteBuf, E> {
                    Ok(ByteBuf(v.to_vec()))
                }
                fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<ByteBuf, E> {
                    Ok(ByteBuf(v))
                }
            }
            d.deserialize_byte_buf(V)
        }
    }
    #[derive(Debug, PartialEq)]
    struct BorrowedBytes<'a>(&'a [u8]);
    impl<'de: 'a, 'a> Deserialize<'de> for BorrowedBytes<'a> {
        fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            struct V;
            impl<'de> Visitor<'de> for V {
                type Value = BorrowedBytes<'de>;
                fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.write_str("borrowed bytes")
                }
                fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<BorrowedBytes<'de>, E> {
                    Ok(BorrowedBytes(v))
                }
            }
            d.deserialize_bytes(V)
        }
    }

    let raw = [1u8, 2, 3];
    let encoded = trust_bincode::serialize(&Bytes(&raw)).unwrap();
    // Fixture observation O6, re-derived: serialize_bytes and Vec<u8> agree.
    assert_eq!(encoded, trust_bincode::serialize(&raw.to_vec()).unwrap());

    assert_eq!(
        trust_bincode::deserialize::<ByteBuf>(&encoded).unwrap(),
        ByteBuf(raw.to_vec())
    );
    assert_eq!(
        trust_bincode::deserialize::<BorrowedBytes<'_>>(&encoded).unwrap(),
        BorrowedBytes(&raw)
    );
}

#[test]
fn slice_decoding_borrows_the_input_zero_copy() {
    let encoded = trust_bincode::serialize(&"hello".to_string()).unwrap();
    let borrowed: &str = trust_bincode::deserialize(&encoded).unwrap();
    assert_eq!(borrowed, "hello");
    // The borrow points INTO the input buffer, not into a copy.
    let base = encoded.as_ptr() as usize;
    let got = borrowed.as_ptr() as usize;
    assert!(
        got >= base && got < base + encoded.len(),
        "expected a borrowed str, got a copy"
    );

    // The reader path cannot borrow; an owned String still round-trips.
    let owned = trust_bincode::deserialize_from::<&[u8], String>(&encoded[..]).unwrap();
    assert_eq!(owned, "hello");
}

// ---------------------------------------------------------------------------
// Error type shape
// ---------------------------------------------------------------------------

#[test]
fn the_error_is_a_boxed_kind_that_callers_can_match_on() {
    // `bincode::Error = Box<ErrorKind>` is API: consumers write
    // `Result<T, bincode::Error>` and some match on `*err`.
    let err: trust_bincode::Error = trust_bincode::deserialize::<bool>(&[2]).unwrap_err();
    match *err {
        ErrorKind::InvalidBoolEncoding(b) => assert_eq!(b, 2),
        ref other => panic!("wrong kind: {other:?}"),
    }
    let e2: trust_bincode::Error = trust_bincode::deserialize::<u32>(&[1, 2]).unwrap_err();
    assert!(matches!(*e2, ErrorKind::Io(_)));
    // It is a std::error::Error, with the io error as its source.
    //
    // NOTE — this is a KNOWN DIVERGENCE, not incumbent parity. `bincode 1.3.3`
    // returns `None` from `source()` for this variant; this crate chains to the
    // underlying `io::Error`. Recorded as divergence 5 in `src/lib.rs`. This
    // assertion deliberately pins OUR behaviour, so read it as "the chaining is
    // intentional and must not regress", never as "the incumbent does this".
    // No encoded byte and no `Display` string differs, so no artifact can
    // observe it.
    let as_std: &dyn std::error::Error = &*e2;
    assert!(as_std.source().is_some());
}

// ---------------------------------------------------------------------------
// A whole-shape round trip through every serde kind reachable from a derive
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize, Debug, PartialEq)]
struct Everything {
    unit: (),
    b: bool,
    i: (i8, i16, i32, i64, i128),
    u: (u8, u16, u32, u64, u128),
    f: (f32, f64),
    c: char,
    s: String,
    v: Vec<Option<u8>>,
    arr: [u32; 3],
    map: BTreeMap<String, Vec<u8>>,
    nested: Option<Box<Everything>>,
    e: Choice,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
enum Choice {
    A,
    B(u32),
    C(u8, u8),
    D { k: String },
}

fn sample(depth: usize) -> Everything {
    Everything {
        unit: (),
        b: depth % 2 == 0,
        i: (-1, -300, -70000, -5_000_000_000, i128::MIN),
        u: (250, 251, 65536, u64::MAX, u128::MAX),
        // NOT a NaN: this value is compared with `assert_eq!`, and NaN != NaN
        // would make the round trip look broken. NaN bit-exactness is covered
        // separately by `nan_bit_patterns_survive_a_round_trip` and by the
        // golden fixture, both of which compare BITS.
        f: (f32::from_bits(0xff7f_ffff), f64::NEG_INFINITY),
        c: '𝄞',
        s: "héllo\0".to_string(),
        v: vec![None, Some(5), None],
        arr: [1, 2, 3],
        map: BTreeMap::from([("k".to_string(), vec![1u8, 2])]),
        nested: if depth == 0 {
            None
        } else {
            Some(Box::new(sample(depth - 1)))
        },
        e: match depth % 4 {
            0 => Choice::A,
            1 => Choice::B(70000),
            2 => Choice::C(1, 2),
            _ => Choice::D {
                k: "z".to_string(),
            },
        },
    }
}

#[test]
fn every_serde_kind_round_trips_under_all_four_int_endian_combinations() {
    let value = sample(3);
    macro_rules! rt {
        ($cfg:expr) => {{
            let bytes = $cfg.serialize(&value).unwrap();
            assert_eq!($cfg.serialized_size(&value).unwrap(), bytes.len() as u64);
            let back: Everything = $cfg.deserialize(&bytes).unwrap();
            assert_eq!(back, value);
            let back: Everything = $cfg.deserialize_from(&bytes[..]).unwrap();
            assert_eq!(back, value);
            bytes
        }};
    }
    let fl = rt!(DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .reject_trailing_bytes());
    let fb = rt!(DefaultOptions::new()
        .with_fixint_encoding()
        .with_big_endian()
        .reject_trailing_bytes());
    let vl = rt!(DefaultOptions::new()
        .with_varint_encoding()
        .with_little_endian()
        .reject_trailing_bytes());
    let vb = rt!(DefaultOptions::new()
        .with_varint_encoding()
        .with_big_endian()
        .reject_trailing_bytes());

    // The four really are four: nothing has silently collapsed to one config.
    let all = [&fl, &fb, &vl, &vb];
    for i in 0..all.len() {
        for j in (i + 1)..all.len() {
            assert_ne!(all[i], all[j], "configs {i} and {j} produced identical bytes");
        }
    }
    // And varint is genuinely shorter here (the values were chosen so).
    assert!(vl.len() < fl.len());
}

#[test]
fn nan_bit_patterns_survive_a_round_trip_exactly() {
    // The format writes raw IEEE-754 bits, so quiet NaNs, signalling NaNs and
    // the NaN sign bit all survive. Compared as BITS, because NaN != NaN.
    for bits in [0x7fc0_0000u32, 0xffc0_0000, 0x7f80_0001, 0x7f80_0000, 0xff80_0000] {
        let v = f32::from_bits(bits);
        let back: f32 = trust_bincode::deserialize(&trust_bincode::serialize(&v).unwrap()).unwrap();
        assert_eq!(back.to_bits(), bits, "f32 bits 0x{bits:08x}");
    }
    for bits in [
        0x7ff8_0000_0000_0000u64,
        0xfff8_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0x7ff0_0000_0000_0000,
    ] {
        let v = f64::from_bits(bits);
        let back: f64 = trust_bincode::deserialize(&trust_bincode::serialize(&v).unwrap()).unwrap();
        assert_eq!(back.to_bits(), bits, "f64 bits 0x{bits:016x}");
    }
}

#[test]
fn the_documented_examples_actually_run() {
    // The examples in `lib.rs` and `config/mod.rs`, copied verbatim as real
    // tests.
    //
    // WHY: `targo test -p trust-bincode --doc` does not run in this tree — it
    // dies with SIGABRT inside `trustdoc` — and it does so for the CONTROL
    // crate `trust-toml` identically, so this is an environment condition and
    // not something about this crate. Either way a doc example is not
    // evidence while the doctest runner is dead, so the examples are pinned
    // here, with their exact bytes so the assertion cannot pass under a wrong
    // int encoding.
    let target: Option<String> = Some("hello world".to_string());
    let encoded: Vec<u8> = trust_bincode::serialize(&target).unwrap();
    assert_eq!(
        encoded,
        vec![
            0x01, // Some
            0x0b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // len 11, fixint LE
            b'h', b'e', b'l', b'l', b'o', b' ', b'w', b'o', b'r', b'l', b'd',
        ]
    );
    let decoded: Option<String> = trust_bincode::deserialize(&encoded[..]).unwrap();
    assert_eq!(target, decoded);

    let my_options = DefaultOptions::new()
        .with_fixint_encoding()
        .allow_trailing_bytes();
    assert_eq!(my_options.serialize(&target).unwrap(), encoded);
}
