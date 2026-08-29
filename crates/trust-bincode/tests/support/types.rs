// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The types the golden fixture's cases are values of.
//!
//! Their SHAPES were recovered from the captured bytes, not guessed: e.g.
//! `NamedStruct` is `{ a: u8, b: String, c: Vec<u8> }` because
//! `named_struct` is `01 | 0200000000000000 6162 | 0200000000000000 0909`
//! under the fixint config.
//!
//! Three of these carry hand-written `Serialize`/`Deserialize` impls rather
//! than derives, and each replaces a third-party crate the capture used:
//!
//! * `Bytes` calls `serialize_bytes` — the capture used `serde_bytes::ByteBuf`.
//!   Observation O6 in the fixture records that `serde_bytes` and `Vec<u8>`
//!   produce identical bytes, so this reaches the same encoder path with no
//!   dependency.
//! * `UnknownLenSeq` calls `serialize_seq(None)` — the only way to reach
//!   `SequenceMustHaveLength`.
//! * `AnyValue` calls `deserialize_any` — the capture used
//!   `serde_json::Value`, whose `Deserialize` does the same thing. The error
//!   under test is this crate's `DeserializeAnyNotSupported`, not serde_json's.

use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

pub use crate::support::big_enum::BigEnum;

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct UnitStruct;

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct NewtypeStruct(pub u32);

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct TupleStruct(pub u8, pub String);

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct NamedStruct {
    pub a: u8,
    pub b: String,
    pub c: Vec<u8>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct NestedStruct {
    pub inner: NamedStruct,
    pub opt: Option<u8>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub enum E3 {
    A,
    B,
    C,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub enum Mixed {
    Unit,
    New(u32),
    Tup(u8, u8),
    Struct { x: u8, y: String },
}

/// `Leaf` MUST be index 0 and `Node` index 1 — the captured deep-nesting
/// bytes are `01` repeated then `00 07`.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub enum Nest {
    Leaf(u8),
    Node(Box<Nest>),
}

pub fn nest(depth: usize, leaf: u8) -> Nest {
    let mut n = Nest::Leaf(leaf);
    for _ in 0..depth {
        n = Nest::Node(Box::new(n));
    }
    n
}

/// Reaches `Serializer::serialize_bytes`.
pub struct Bytes(pub Vec<u8>);

impl Serialize for Bytes {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.0)
    }
}

/// Reaches `ErrorKind::SequenceMustHaveLength`.
pub struct UnknownLenSeq;

impl Serialize for UnknownLenSeq {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        let mut seq = serializer.serialize_seq(None)?;
        seq.serialize_element(&1u8)?;
        seq.end()
    }
}

/// Reaches `Deserializer::deserialize_any`.
#[derive(Debug, PartialEq)]
pub struct AnyValue;

impl<'de> Deserialize<'de> for AnyValue {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = AnyValue;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("any value")
            }
            fn visit_u8<E>(self, _v: u8) -> Result<AnyValue, E> {
                Ok(AnyValue)
            }
        }
        deserializer.deserialize_any(V)
    }
}
