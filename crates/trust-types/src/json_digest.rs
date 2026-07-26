//! Wide-integer-tolerant canonical JSON digest material.
//!
//! Trust (falsification corpus, i128/u128 ICE class): the verifier-api digest
//! sites (`vc_content_digest` / `contract_predicate_digest` in
//! trust-mir-extract) canonicalize their material through
//! `serde_json::to_value`, and `serde_json::Value` cannot represent integers
//! outside the i64/u64 range. Any VC formula carrying i128/u128 type-range
//! literals — the `i128::MIN`/`i128::MAX` bounds every i128 overflow VC
//! contains — made `to_value` fail with "number out of range", and the
//! fail-closed `expect` turned that into a compiler ICE on ordinary,
//! fully-representable source. The verifier must never crash on material the
//! Formula model can express.
//!
//! Two layers now uphold the wide-integer digest identity, in this order:
//!
//! 1. **Formula self-encoding** (trust-ir-contract `wide_i128`/`wide_u128`
//!    serde helpers, 65e651d, 2026-07-18 — the fix at the source): on
//!    human-readable serializers a `Formula` wide literal serializes as its
//!    bare decimal STRING (`{"Int": "-1701…"}`), so `serde_json::to_value`
//!    succeeds and the fast path defines Formula wide identity. In-range
//!    literals stay bare numbers — byte-identical to the historical derive —
//!    and the two encodings cannot collide: a wide literal's decimal is
//!    outside any range a bare JSON number here can render, and string vs
//!    number differ bytewise regardless.
//! 2. **This module's tagged fallback** (the backstop): digest material whose
//!    `Serialize` emits a RAW out-of-range `serialize_i128`/`serialize_u128`
//!    call (no Formula-level encoding in front) still fails `to_value`;
//!    [`canonical_digest_json_value`] then re-serializes with
//!    [`WideIntDigestSerializer`], which reproduces the `serde_json`
//!    value-serializer encoding exactly except that an integer outside
//!    JSON-number range becomes a tagged singleton object, e.g.
//!    `{"$trust.digest.i128": "-170141183460469231731687303715884105728"}`.
//!
//! Digest material needs only DETERMINISM and INJECTIVITY, not
//! JSON-number-ness, and the two forms provide both:
//!
//! * determinism: both lanes are pure functions of the input, and the
//!   out-of-range-number guard (below) makes the OUTPUT independent of which
//!   lane ran;
//! * identity stability: every value that digested under the historical bare
//!   `to_value` algorithm still takes the fast path unchanged, so its digest
//!   bytes are IDENTICAL — only inputs that previously had NO digest at all
//!   (they panicked) gained one. Identity history for the wide tail: between
//!   2026-07-17 (this module landed; wide `Formula` literals took the tagged
//!   form) and 2026-07-18 (submodule pin 241bba23f72 brought in layer 1),
//!   wide `Formula` digests flipped from the tagged form to the Formula
//!   decimal-string form. Nothing persisted either identity (the class ICE'd
//!   before 07-17; no fixture/golden/cache embeds either form), and the
//!   golden tests below pin the CURRENT bytes so any future flip is loud;
//! * version stability (the fail-closed guard): the returned `Value` never
//!   contains a native out-of-JSON-range number, under ANY serde_json
//!   behavior. Lane selection is "does `to_value` fail", which is a property
//!   of the serde_json VERSION: a future serde_json that materializes
//!   i128/u128 natively would silently switch raw wide material from the
//!   tagged form to native numbers — an evidence-identity drift.
//!   `contains_out_of_json_range_number` reroutes any such fast-path result
//!   to the wide lane (whose bytes equal today's fallback bytes) and refuses,
//!   fail-closed BEFORE the caller hashes, a wide-lane result that still
//!   carries one;
//! * injectivity within the fallback lane: the encoding is the serde_json one
//!   plus an injective tag per out-of-range integer (distinct keys keep
//!   `serialize_i128` and `serialize_u128` distinguishable, the decimal
//!   rendering is injective per key);
//! * injectivity ACROSS the forms: a fast-path output can only contain
//!   `{"$trust.digest.i128": <string>}` if the input itself serializes a
//!   free-form string-keyed map with that exact key — the tag keys contain
//!   `$` and `.`, which no Rust field or variant identifier can produce, so
//!   only map-typed payloads could forge them. The digested material types
//!   uphold this by construction: `Formula` (the wide-int carrier) has no
//!   map-typed payloads, and the map-carrying digest inputs
//!   (`ContractPredicate`'s `serde_json::Value` payloads) cannot hold an
//!   out-of-range integer at this serde_json version — and if a future
//!   `Value` could, the guard reroutes it to the wide lane, where the
//!   `Number`'s own `serialize_i128` call lands in the tagged form. Callers
//!   adding NEW digest material types must preserve that separation.
//!
//! Failure of the fallback (non-string map keys, a `Serialize` impl that
//! errors) surfaces as an error — behavior identical to before, and the
//! caller's fail-closed `expect` still refuses a debug-shaped fallback
//! identity. This module can only turn "ICE" into "digested", never change an
//! existing digest.

use serde::ser::{Impossible, Serialize};
use serde_json::{Error, Map, Value};

/// Tag key for an `i128` outside the JSON-number (i64/u64) range.
///
/// Contains `$` and `.` so no Rust field/variant identifier (and therefore no
/// derived serialization of the digest material types) can collide with it.
pub const WIDE_I128_DIGEST_TAG_KEY: &str = "$trust.digest.i128";

/// Tag key for a `u128` outside the JSON-number (u64) range.
pub const WIDE_U128_DIGEST_TAG_KEY: &str = "$trust.digest.u128";

/// Canonical JSON digest form of one piece of digest material.
///
/// Fast path: `serde_json::to_value` (byte-identical to the historical digest
/// encoding). Fallback on ANY fast-path failure: the wide-integer-tolerant
/// [`WideIntDigestSerializer`]. The fallback is retried on every failure
/// rather than string-matching the error: it diverges from `to_value` only on
/// out-of-range i128/u128, so a failure with any other cause fails the
/// fallback identically and no new input becomes silently digestible.
///
/// Fail-closed identity guard, applied BEFORE the caller hashes: a result
/// carrying a native out-of-JSON-range number is never returned. At this
/// serde_json version the fast path cannot produce one (`to_value` rejects
/// wide integers), so the guard is byte-neutral today; its job is to keep
/// lane selection — and therefore digest identity — independent of whether a
/// FUTURE serde_json starts materializing i128/u128 natively. A tripped
/// fast-path guard reroutes to the wide lane (identical bytes to today's
/// fallback); a tripped wide-lane guard is an error, because no lane may
/// define a version-dependent identity.
pub fn canonical_digest_json_value<T>(value: &T) -> Result<Value, Error>
where
    T: ?Sized + Serialize,
{
    match serde_json::to_value(value) {
        Ok(fast) if !contains_out_of_json_range_number(&fast) => Ok(fast),
        _ => {
            let wide = value.serialize(WideIntDigestSerializer)?;
            if contains_out_of_json_range_number(&wide) {
                return Err(serde::ser::Error::custom(
                    "digest canonicalization produced a native out-of-JSON-range number; \
                     refusing a version-dependent digest identity",
                ));
            }
            Ok(wide)
        }
    }
}

/// True iff the tree contains a `Number` that is not representable as
/// i64/u64/f64 — i.e. a native wide integer that would give digest bytes a
/// serde_json-version-dependent identity. Representation-based (`is_*`, not
/// lossy `as_f64` conversion) so a future native i128 `Number` cannot hide
/// behind an approximate float view.
fn contains_out_of_json_range_number(value: &Value) -> bool {
    match value {
        Value::Number(number) => !(number.is_i64() || number.is_u64() || number.is_f64()),
        Value::Array(items) => items.iter().any(contains_out_of_json_range_number),
        Value::Object(map) => map.values().any(contains_out_of_json_range_number),
        Value::Null | Value::Bool(_) | Value::String(_) => false,
    }
}

fn wide_int_tag(key: &'static str, decimal: String) -> Value {
    let mut object = Map::with_capacity(1);
    object.insert(key.to_owned(), Value::String(decimal));
    Value::Object(object)
}

fn key_must_be_a_string() -> Error {
    serde::ser::Error::custom("wide-int digest material map key must be a string")
}

/// `serde_json::value::Serializer` with out-of-range i128/u128 tagged instead
/// of rejected.
///
/// Every arm below MUST stay observably identical to serde_json's value
/// serializer (see `serde_json/src/value/ser.rs`) except `serialize_i128` /
/// `serialize_u128`: the fallback lane's output for the in-range PARTS of a
/// mixed value defines digest identity for formulas that never had one, and
/// the byte-compat differential test pins the equivalence on fully-in-range
/// inputs. Float map keys are the one deliberate omission (serde_json accepts
/// finite ones): no digest material type has float-keyed maps, and an
/// unsupported key errors fail-closed rather than inventing an encoding.
struct WideIntDigestSerializer;

fn to_wide_value<T>(value: &T) -> Result<Value, Error>
where
    T: ?Sized + Serialize,
{
    value.serialize(WideIntDigestSerializer)
}

impl serde::Serializer for WideIntDigestSerializer {
    type Ok = Value;
    type Error = Error;

    type SerializeSeq = SerializeWideVec;
    type SerializeTuple = SerializeWideVec;
    type SerializeTupleStruct = SerializeWideVec;
    type SerializeTupleVariant = SerializeWideTupleVariant;
    type SerializeMap = SerializeWideMap;
    type SerializeStruct = SerializeWideMap;
    type SerializeStructVariant = SerializeWideStructVariant;

    fn serialize_bool(self, value: bool) -> Result<Value, Error> {
        Ok(Value::Bool(value))
    }

    fn serialize_i8(self, value: i8) -> Result<Value, Error> {
        self.serialize_i64(i64::from(value))
    }

    fn serialize_i16(self, value: i16) -> Result<Value, Error> {
        self.serialize_i64(i64::from(value))
    }

    fn serialize_i32(self, value: i32) -> Result<Value, Error> {
        self.serialize_i64(i64::from(value))
    }

    fn serialize_i64(self, value: i64) -> Result<Value, Error> {
        Ok(Value::Number(value.into()))
    }

    // The point of the lane: an in-range wide integer keeps the exact
    // serde_json Number encoding (same u64-first probe order); an
    // out-of-range one becomes the injective tagged form instead of the
    // "number out of range" error that ICE'd the verifier.
    fn serialize_i128(self, value: i128) -> Result<Value, Error> {
        if let Ok(value) = u64::try_from(value) {
            Ok(Value::Number(value.into()))
        } else if let Ok(value) = i64::try_from(value) {
            Ok(Value::Number(value.into()))
        } else {
            Ok(wide_int_tag(WIDE_I128_DIGEST_TAG_KEY, value.to_string()))
        }
    }

    fn serialize_u8(self, value: u8) -> Result<Value, Error> {
        self.serialize_u64(u64::from(value))
    }

    fn serialize_u16(self, value: u16) -> Result<Value, Error> {
        self.serialize_u64(u64::from(value))
    }

    fn serialize_u32(self, value: u32) -> Result<Value, Error> {
        self.serialize_u64(u64::from(value))
    }

    fn serialize_u64(self, value: u64) -> Result<Value, Error> {
        Ok(Value::Number(value.into()))
    }

    fn serialize_u128(self, value: u128) -> Result<Value, Error> {
        if let Ok(value) = u64::try_from(value) {
            Ok(Value::Number(value.into()))
        } else {
            Ok(wide_int_tag(WIDE_U128_DIGEST_TAG_KEY, value.to_string()))
        }
    }

    // serde_json parity: non-finite floats canonicalize to Null.
    fn serialize_f32(self, float: f32) -> Result<Value, Error> {
        Ok(Value::from(float))
    }

    fn serialize_f64(self, float: f64) -> Result<Value, Error> {
        Ok(Value::from(float))
    }

    fn serialize_char(self, value: char) -> Result<Value, Error> {
        Ok(Value::String(value.to_string()))
    }

    fn serialize_str(self, value: &str) -> Result<Value, Error> {
        Ok(Value::String(value.to_owned()))
    }

    fn serialize_bytes(self, value: &[u8]) -> Result<Value, Error> {
        Ok(Value::Array(value.iter().map(|&byte| Value::Number(byte.into())).collect()))
    }

    fn serialize_unit(self) -> Result<Value, Error> {
        Ok(Value::Null)
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Value, Error> {
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Value, Error> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<Value, Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Value, Error>
    where
        T: ?Sized + Serialize,
    {
        let mut object = Map::with_capacity(1);
        object.insert(variant.to_owned(), to_wide_value(value)?);
        Ok(Value::Object(object))
    }

    fn serialize_none(self) -> Result<Value, Error> {
        self.serialize_unit()
    }

    fn serialize_some<T>(self, value: &T) -> Result<Value, Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Error> {
        Ok(SerializeWideVec { vec: Vec::with_capacity(len.unwrap_or(0)) })
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Error> {
        Ok(SerializeWideTupleVariant { name: variant.to_owned(), vec: Vec::with_capacity(len) })
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Error> {
        Ok(SerializeWideMap { map: Map::with_capacity(len.unwrap_or(0)), next_key: None })
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Error> {
        self.serialize_map(Some(len))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Error> {
        Ok(SerializeWideStructVariant { name: variant.to_owned(), map: Map::new() })
    }

    fn collect_str<T>(self, value: &T) -> Result<Value, Error>
    where
        T: ?Sized + std::fmt::Display,
    {
        Ok(Value::String(value.to_string()))
    }
}

struct SerializeWideVec {
    vec: Vec<Value>,
}

impl serde::ser::SerializeSeq for SerializeWideVec {
    type Ok = Value;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        self.vec.push(to_wide_value(value)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        Ok(Value::Array(self.vec))
    }
}

impl serde::ser::SerializeTuple for SerializeWideVec {
    type Ok = Value;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        serde::ser::SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Value, Error> {
        serde::ser::SerializeSeq::end(self)
    }
}

impl serde::ser::SerializeTupleStruct for SerializeWideVec {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        serde::ser::SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Value, Error> {
        serde::ser::SerializeSeq::end(self)
    }
}

struct SerializeWideTupleVariant {
    name: String,
    vec: Vec<Value>,
}

impl serde::ser::SerializeTupleVariant for SerializeWideTupleVariant {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        self.vec.push(to_wide_value(value)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        let mut object = Map::with_capacity(1);
        object.insert(self.name, Value::Array(self.vec));
        Ok(Value::Object(object))
    }
}

struct SerializeWideMap {
    map: Map<String, Value>,
    next_key: Option<String>,
}

impl serde::ser::SerializeMap for SerializeWideMap {
    type Ok = Value;
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        self.next_key = Some(key.serialize(WideMapKeySerializer)?);
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        let key = self.next_key.take().expect("serialize_value called before serialize_key");
        self.map.insert(key, to_wide_value(value)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        Ok(Value::Object(self.map))
    }
}

impl serde::ser::SerializeStruct for SerializeWideMap {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        serde::ser::SerializeMap::serialize_entry(self, key, value)
    }

    fn end(self) -> Result<Value, Error> {
        serde::ser::SerializeMap::end(self)
    }
}

struct SerializeWideStructVariant {
    name: String,
    map: Map<String, Value>,
}

impl serde::ser::SerializeStructVariant for SerializeWideStructVariant {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        self.map.insert(key.to_owned(), to_wide_value(value)?);
        Ok(())
    }

    fn end(self) -> Result<Value, Error> {
        let mut object = Map::with_capacity(1);
        object.insert(self.name, Value::Object(self.map));
        Ok(Value::Object(object))
    }
}

/// Map-key lane of [`WideIntDigestSerializer`]: string-like keys only, decimal
/// rendering for integer keys (integer keys are ALWAYS in-range as strings, so
/// wide integers need no tag here), fail-closed on everything else. Mirrors
/// serde_json's `MapKeySerializer` minus float keys (deliberate; see the
/// serializer note above).
struct WideMapKeySerializer;

macro_rules! wide_key_display {
    ($($method:ident: $ty:ty,)*) => {
        $(
            fn $method(self, value: $ty) -> Result<String, Error> {
                Ok(value.to_string())
            }
        )*
    };
}

impl serde::Serializer for WideMapKeySerializer {
    type Ok = String;
    type Error = Error;

    type SerializeSeq = Impossible<String, Error>;
    type SerializeTuple = Impossible<String, Error>;
    type SerializeTupleStruct = Impossible<String, Error>;
    type SerializeTupleVariant = Impossible<String, Error>;
    type SerializeMap = Impossible<String, Error>;
    type SerializeStruct = Impossible<String, Error>;
    type SerializeStructVariant = Impossible<String, Error>;

    wide_key_display! {
        serialize_i8: i8,
        serialize_i16: i16,
        serialize_i32: i32,
        serialize_i64: i64,
        serialize_i128: i128,
        serialize_u8: u8,
        serialize_u16: u16,
        serialize_u32: u32,
        serialize_u64: u64,
        serialize_u128: u128,
        serialize_char: char,
    }

    fn serialize_bool(self, value: bool) -> Result<String, Error> {
        Ok(if value { "true" } else { "false" }.to_owned())
    }

    fn serialize_str(self, value: &str) -> Result<String, Error> {
        Ok(value.to_owned())
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<String, Error> {
        Ok(variant.to_owned())
    }

    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<String, Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_f32(self, _value: f32) -> Result<String, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_f64(self, _value: f64) -> Result<String, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_bytes(self, _value: &[u8]) -> Result<String, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_unit(self) -> Result<String, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<String, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<String, Error>
    where
        T: ?Sized + Serialize,
    {
        Err(key_must_be_a_string())
    }

    fn serialize_none(self) -> Result<String, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_some<T>(self, _value: &T) -> Result<String, Error>
    where
        T: ?Sized + Serialize,
    {
        Err(key_must_be_a_string())
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Error> {
        Err(key_must_be_a_string())
    }

    fn collect_str<T>(self, value: &T) -> Result<String, Error>
    where
        T: ?Sized + std::fmt::Display,
    {
        Ok(value.to_string())
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::{Formula, RoundingMode, Sort, SourceSpan, Symbol, VcKind};

    /// The i128 overflow VC's type-range guard shape — exactly the material
    /// class that ICE'd trustc on every i128/u128 falsification fixture.
    fn i128_range_guard_formula() -> Formula {
        let x = || Box::new(Formula::Var("x".to_string(), Sort::Int));
        Formula::And(vec![
            Formula::Ge(x(), Box::new(Formula::Int(i128::MIN))),
            Formula::Le(x(), Box::new(Formula::Int(i128::MAX))),
        ])
    }

    /// In-range corpus spanning the serializer surface the digest material
    /// types exercise: literals at every JSON-number boundary, nested
    /// connectives, quantifiers with interned symbols, unit/struct/tuple
    /// variants, and the sibling digest material types (VcKind, SourceSpan).
    fn in_range_formula_corpus() -> Vec<Formula> {
        let var = || Box::new(Formula::Var("x".to_string(), Sort::Int));
        vec![
            Formula::Bool(true),
            Formula::Int(0),
            Formula::Int(-1),
            Formula::Int(i128::from(i64::MIN)),
            Formula::Int(i128::from(u64::MAX)),
            Formula::UInt(0),
            Formula::UInt(u128::from(u64::MAX)),
            Formula::BitVec { value: -5, width: 8 },
            Formula::FpConst { bits: u128::from(u64::MAX), eb: 11, sb: 53 },
            Formula::FpRoundingMode(RoundingMode::RNE),
            Formula::Var("$trust.digest.i128".to_string(), Sort::Bool),
            Formula::SymVar(Symbol::intern("y"), Sort::Bool),
            Formula::Not(Box::new(Formula::Bool(false))),
            Formula::And(vec![Formula::Bool(true), Formula::Gt(var(), Box::new(Formula::Int(7)))]),
            Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(false))),
            Formula::Ite(Box::new(Formula::Bool(true)), var(), Box::new(Formula::Int(2))),
            Formula::Forall(
                vec![(Symbol::intern("q"), Sort::Int)],
                Box::new(Formula::Eq(var(), var())),
            ),
            Formula::Pred(Symbol::intern("dir_open"), vec![Formula::Var("d".into(), Sort::Int)]),
            Formula::BvExtract {
                inner: Box::new(Formula::BitVec { value: 3, width: 8 }),
                high: 7,
                low: 0,
            },
        ]
    }

    #[test]
    fn wide_i128_range_guard_digests_and_is_deterministic() {
        let formula = i128_range_guard_formula();

        let first = canonical_digest_json_value(&formula)
            .expect("i128 type-range guard formula must digest");
        let second = canonical_digest_json_value(&formula)
            .expect("i128 type-range guard formula must digest deterministically");
        assert_eq!(first, second);
        let bytes = serde_json::to_vec(&first).expect("digest value must serialize");
        assert_eq!(bytes, serde_json::to_vec(&second).expect("digest value must serialize"));

        // The invariant, not the mechanism: pin the exact canonical bytes.
        // Wide Formula literals take the Formula decimal-string form (layer 1
        // of the module header). If ANY layer shifts this identity — a
        // serde_json upgrade, a Formula serde change, a lane-selection change
        // — this golden must fail loudly, because these bytes feed evidence
        // identity and the trust-cache.
        assert_eq!(
            String::from_utf8(bytes).expect("canonical JSON is UTF-8"),
            r#"{"And":[{"Ge":[{"Var":["x","Int"]},{"Int":"-170141183460469231731687303715884105728"}]},{"Le":[{"Var":["x","Int"]},{"Int":"170141183460469231731687303715884105727"}]}]}"#,
        );

        // Lane independence: both lanes produce the identical value for this
        // material, so digest identity cannot fork on lane selection.
        assert_eq!(
            formula.serialize(WideIntDigestSerializer).expect("wide lane must serialize"),
            first,
        );
    }

    #[test]
    fn formula_wide_literals_digest_as_decimal_strings() {
        // Formula wide literals self-encode (trust-ir-contract
        // wide_i128/wide_u128) as bare decimal strings on the fast path;
        // in-range literals stay bare numbers, byte-identical to the
        // historical derive. Golden-pinned per wide-carrying variant.
        assert_eq!(
            canonical_digest_json_value(&Formula::Int(i128::MIN)).expect("i128::MIN must digest"),
            json!({"Int": "-170141183460469231731687303715884105728"}),
        );
        assert_eq!(
            canonical_digest_json_value(&Formula::UInt(u128::MAX)).expect("u128::MAX must digest"),
            json!({"UInt": "340282366920938463463374607431768211455"}),
        );
        assert_eq!(
            canonical_digest_json_value(&Formula::BitVec { value: i128::MIN, width: 128 })
                .expect("wide BitVec literal must digest"),
            json!({"BitVec": {"value": "-170141183460469231731687303715884105728", "width": 128}}),
        );
        assert_eq!(
            canonical_digest_json_value(&Formula::FpConst { bits: u128::MAX, eb: 15, sb: 113 })
                .expect("wide FpConst bits must digest"),
            json!({"FpConst": {"bits": "340282366920938463463374607431768211455", "eb": 15, "sb": 113}}),
        );
        // In-range literals stay bare numbers — the string form cannot shadow
        // them (string vs number differ bytewise; decimals are disjoint).
        assert_eq!(canonical_digest_json_value(&Formula::Int(7)).unwrap(), json!({"Int": 7}));
        assert_eq!(canonical_digest_json_value(&Formula::Int(-7)).unwrap(), json!({"Int": -7}));
    }

    #[test]
    fn wide_int_literals_take_the_tagged_form() {
        // The backstop class (layer 2): digest material whose Serialize emits
        // a RAW out-of-range serialize_i128/serialize_u128 call — no
        // Formula-level string encoding in front — gets the injective tagged
        // identity from this module's wide lane.
        assert_eq!(
            canonical_digest_json_value(&i128::MIN).expect("raw i128::MIN must digest"),
            json!({"$trust.digest.i128": "-170141183460469231731687303715884105728"}),
        );
        assert_eq!(
            canonical_digest_json_value(&u128::MAX).expect("raw u128::MAX must digest"),
            json!({"$trust.digest.u128": "340282366920938463463374607431768211455"}),
        );
        // In-range raw 128-bit ints keep serde_json's bare-number identity.
        assert_eq!(canonical_digest_json_value(&-5i128).unwrap(), json!(-5));
        assert_eq!(canonical_digest_json_value(&u128::from(u64::MAX)).unwrap(), json!(u64::MAX));
        // Nested position: only the wide leaf is tagged.
        assert_eq!(
            canonical_digest_json_value(&(i128::MIN, 1u8)).expect("mixed tuple must digest"),
            json!([{"$trust.digest.i128": "-170141183460469231731687303715884105728"}, 1]),
        );
    }

    #[test]
    fn in_range_material_is_byte_identical_to_the_historical_algorithm() {
        // Must-NOT twin: everything that digested before this change must
        // produce the exact same bytes — on BOTH lanes, because the fallback
        // lane's encoding of the in-range PARTS of a mixed value must equal
        // the fast path's.
        for formula in in_range_formula_corpus() {
            let fast = serde_json::to_value(&formula).expect("corpus is in-range");
            let canonical = canonical_digest_json_value(&formula).expect("corpus must digest");
            let wide_lane = formula.serialize(WideIntDigestSerializer).expect("wide lane");
            assert_eq!(canonical, fast, "fast-path identity changed for {formula:?}");
            assert_eq!(wide_lane, fast, "wide-lane encoding diverged for {formula:?}");
            assert_eq!(
                serde_json::to_vec(&wide_lane).expect("serializable"),
                serde_json::to_vec(&fast).expect("serializable"),
                "wide-lane bytes diverged for {formula:?}",
            );
        }

        // Sibling digest material types (vc.kind / vc.location / contract.span).
        let span = SourceSpan {
            file: "demo.rs".to_string(),
            line_start: 3,
            col_start: 1,
            line_end: 4,
            col_end: 9,
        };
        let kind = VcKind::DivisionByZero;
        for (fast, wide) in [
            (
                serde_json::to_value(&span).unwrap(),
                span.serialize(WideIntDigestSerializer).unwrap(),
            ),
            (
                serde_json::to_value(&kind).unwrap(),
                kind.serialize(WideIntDigestSerializer).unwrap(),
            ),
        ] {
            assert_eq!(fast, wide);
        }

        // serde_json quirk parity: non-finite floats canonicalize to Null on
        // both lanes (a silent encoding divergence here would fork digest
        // identity the day a float-carrying type joins the digest material).
        assert_eq!(f64::NAN.serialize(WideIntDigestSerializer).unwrap(), Value::Null);
        assert_eq!(serde_json::to_value(f64::NAN).unwrap(), Value::Null);
        assert_eq!(f32::NEG_INFINITY.serialize(WideIntDigestSerializer).unwrap(), Value::Null);
    }

    #[test]
    fn wide_digest_values_stay_injective() {
        // Must-NOT twin: neighbors and cross-sign/width reinterpretations of
        // the same decimal magnitude must never collapse to one identity.
        let min = canonical_digest_json_value(&Formula::Int(i128::MIN)).unwrap();
        let min_succ = canonical_digest_json_value(&Formula::Int(i128::MIN + 1)).unwrap();
        assert_ne!(min, min_succ);

        // Cross-sort reinterpretation at the same decimal magnitude. Under
        // the Formula decimal-string form the PAYLOADS coincide by design
        // (both render the bare decimal), so the variant key is the sort
        // separator — pin the full-value identity, which is what the digest
        // hashes.
        let wide = u128::from(u64::MAX) + 1;
        let as_int = canonical_digest_json_value(&Formula::Int(wide as i128)).unwrap();
        let as_uint = canonical_digest_json_value(&Formula::UInt(wide)).unwrap();
        assert_ne!(as_int, as_uint);
        assert_ne!(
            serde_json::to_vec(&as_int).unwrap(),
            serde_json::to_vec(&as_uint).unwrap(),
        );

        // On the raw/tagged lane the sort separation lives in the tag key
        // itself: serialize_i128 and serialize_u128 stay distinguishable even
        // with no variant wrapper at all.
        let raw_int = canonical_digest_json_value(&(wide as i128)).unwrap();
        let raw_uint = canonical_digest_json_value(&wide).unwrap();
        assert_ne!(raw_int, raw_uint);

        // A Formula that merely NAMES the tag key cannot forge a wide
        // literal's identity: Var payloads are arrays under the "Var"
        // variant, never a bare tagged object.
        let forged_name = canonical_digest_json_value(&Formula::Var(
            WIDE_I128_DIGEST_TAG_KEY.to_string(),
            Sort::Int,
        ))
        .unwrap();
        assert_ne!(forged_name, min);
        assert!(forged_name.get("Var").is_some());

        // A plain STRING of the decimal cannot forge a raw tagged wide int.
        assert_ne!(
            canonical_digest_json_value(&i128::MIN.to_string()).unwrap(),
            canonical_digest_json_value(&i128::MIN).unwrap(),
        );
    }

    #[test]
    fn native_wide_json_numbers_never_reach_digest_bytes() {
        // THE regression pin for the invariant itself: whatever serde_json's
        // native wide-integer capability does across versions, the canonical
        // digest value must never carry a number outside the i64/u64/f64
        // representable range — wide integers reach digest bytes only as
        // quoted decimal strings (Formula form) or tagged objects (raw form).
        let wide_corpus = [
            canonical_digest_json_value(&i128_range_guard_formula()).unwrap(),
            canonical_digest_json_value(&Formula::Int(i128::MIN)).unwrap(),
            canonical_digest_json_value(&Formula::UInt(u128::MAX)).unwrap(),
            canonical_digest_json_value(&Formula::BitVec { value: i128::MIN, width: 128 })
                .unwrap(),
            canonical_digest_json_value(&Formula::FpConst { bits: u128::MAX, eb: 15, sb: 113 })
                .unwrap(),
            canonical_digest_json_value(&i128::MIN).unwrap(),
            canonical_digest_json_value(&u128::MAX).unwrap(),
        ];
        for value in &wide_corpus {
            assert!(
                !contains_out_of_json_range_number(value),
                "native wide number leaked into digest value: {value}",
            );
            // Byte-level pin: every occurrence of a wide decimal in the
            // serialized digest bytes must sit inside a JSON string
            // (immediately preceded by an opening quote), never as a bare
            // JSON number token.
            let bytes = serde_json::to_string(value).expect("digest value must serialize");
            for decimal in [
                "-170141183460469231731687303715884105728",
                "170141183460469231731687303715884105727",
                "340282366920938463463374607431768211455",
            ] {
                let mut from = 0;
                while let Some(found) = bytes[from..].find(decimal) {
                    let at = from + found;
                    assert_eq!(
                        bytes.as_bytes().get(at.wrapping_sub(1)),
                        Some(&b'"'),
                        "wide decimal appears outside a JSON string in {bytes}",
                    );
                    from = at + decimal.len();
                }
            }
        }

        // Guard sanity: nothing representable trips it (the guard must stay
        // byte-neutral for all material that digests today).
        assert!(!contains_out_of_json_range_number(&json!({
            "a": [1, -1, 1.5, u64::MAX, i64::MIN, null, true, "s"],
        })));
        for formula in in_range_formula_corpus() {
            assert!(!contains_out_of_json_range_number(
                &canonical_digest_json_value(&formula).unwrap()
            ));
        }
    }

    #[test]
    fn unserializable_material_still_fails_closed() {
        // Must-NOT twin: the fallback lane must never turn "unserializable"
        // into a fabricated identity. A non-string-keyed map fails the fast
        // path AND the wide lane; the caller's expect stays the crash-stop.
        let mut bad_key = std::collections::BTreeMap::new();
        bad_key.insert((1u8, 2u8), i128::MIN);
        assert!(serde_json::to_value(&bad_key).is_err());
        assert!(canonical_digest_json_value(&bad_key).is_err());
    }

    #[test]
    fn integer_map_keys_keep_serde_json_decimal_identity() {
        // serde_json stringifies integer map keys; the wide lane must render
        // the identical decimal (keys are strings, so even out-of-range wide
        // integers need no tag in key position).
        let mut map = std::collections::BTreeMap::new();
        map.insert(42u64, Formula::Int(i128::MIN));
        let digested = canonical_digest_json_value(&map).expect("integer-keyed map must digest");
        assert!(digested.get("42").is_some());

        let mut in_range = std::collections::BTreeMap::new();
        in_range.insert(-7i64, 1u8);
        assert_eq!(
            in_range.serialize(WideIntDigestSerializer).unwrap(),
            serde_json::to_value(&in_range).unwrap(),
        );
    }
}
