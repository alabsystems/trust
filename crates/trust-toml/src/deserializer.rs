// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The serde [`Deserializer`](serde::Deserializer) over a parsed document.
//!
//! # This is the whole integration mechanism
//!
//! Nothing in this tree is asked to change a `#[derive(Deserialize)]`, a
//! `#[serde(default)]` or a `#[serde(rename_all = "kebab-case")]`. Those are
//! implemented by `serde_derive`, which emits code against the
//! `serde::Deserializer` / `serde::de::Visitor` traits — so a new TOML reader
//! is exactly "a type implementing `Deserializer`", and every consumer keeps
//! compiling verbatim under a Cargo dependency rename. That is why this crate
//! depends on `serde`: not for a data format, for a trait ABI.
//!
//! It also means the container/field attribute surface is *not* this crate's
//! problem. Measured across `crates/` + `targo-trust/`: 1757 `#[serde(...)]`
//! attributes over exactly 15 distinct keys, 1461 derived types. All of it is
//! `serde_derive`'s code calling the methods below.
//!
//! # Most methods forward to `deserialize_any`, deliberately
//!
//! TOML is self-describing: the document already says whether a value is an
//! integer or a string, so `deserialize_u32` has no more information to work
//! with than `deserialize_any` does. Forwarding means the *visitor* decides
//! what conversions are acceptable — and the visitor is serde's, shared with
//! every other self-describing format. Doing our own numeric widening here
//! would be a second, divergent set of coercion rules; forwarding keeps
//! `u32::deserialize` behaving identically whether the bytes came from TOML or
//! from JSON, and identically to the incumbent, which forwards for the same
//! reason.
//!
//! The four methods that do NOT forward are the four where TOML carries
//! information serde's data model cannot express positionally:
//! [`Deserializer::deserialize_option`] (a present key is always `Some`; TOML
//! has no null), `deserialize_newtype_struct` (transparent), `deserialize_enum`
//! (a string is a unit variant, a one-key table is a data variant), and
//! `deserialize_struct` (which intercepts the reserved datetime struct name).
//!
//! # Errors acquire their position on the way out
//!
//! `serde_derive`'s generated code raises `unknown field`, `missing field` and
//! `invalid type` through [`serde::de::Error::custom`], which takes a message
//! and nothing else — no span, because the derived code has no idea what a span
//! is. Every accessor here therefore attaches what it knows as the error
//! unwinds: a map entry attaches its key and its value's position, a sequence
//! element attaches its own, and `deserialize_struct` attaches the enclosing
//! table's as a last resort. All of it is fill-if-absent, so the innermost
//! frame that knows a fact wins.

use serde::de::IntoDeserializer as _;

use crate::datetime::{DATETIME_PRIVATE_FIELD, DATETIME_PRIVATE_NAME, Datetime};
use crate::error::Error;
use crate::map::Map;
use crate::parser::{Item, Kind};

/// A deserializer over one parsed node.
pub(crate) struct ItemDeserializer {
    item: Item,
}

impl ItemDeserializer {
    pub(crate) fn new(item: Item) -> Self {
        Self { item }
    }

    fn position(&self) -> (usize, usize) {
        (self.item.line, self.item.column)
    }

    /// Present a datetime as the reserved one-entry map. See `crate::datetime`
    /// for why the encoding is what it is.
    fn deserialize_datetime<'de, V: serde::de::Visitor<'de>>(
        datetime: Datetime,
        visitor: V,
    ) -> Result<V::Value, Error> {
        visitor.visit_map(DatetimeMapAccess { value: Some(datetime.to_string()) })
    }
}

impl<'de> serde::Deserializer<'de> for ItemDeserializer {
    type Error = Error;

    fn deserialize_any<V: serde::de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Error> {
        let (line, column) = self.position();
        let result = match self.item.kind {
            Kind::String(value) => visitor.visit_string(value),
            Kind::Integer(value) => visitor.visit_i64(value),
            Kind::Float(value) => visitor.visit_f64(value),
            Kind::Boolean(value) => visitor.visit_bool(value),
            Kind::Datetime(value) => Self::deserialize_datetime(value, visitor),
            Kind::Array(items) => visitor.visit_seq(ArraySeqAccess { iter: items.into_iter() }),
            Kind::Table(table) => {
                visitor.visit_map(TableMapAccess { iter: table.into_iter(), pending: None })
            }
        };
        // An `invalid type` raised by the visitor has no position of its own;
        // this node's is the right one. Fill-if-absent, so a nested failure
        // keeps the deeper position it already recorded.
        result.map_err(|error| error.with_position(line, column))
    }

    fn deserialize_option<V: serde::de::Visitor<'de>>(self, visitor: V) -> Result<V::Value, Error> {
        // TOML cannot express a null, so a value that is present is present.
        // A key that is absent never reaches a deserializer at all: serde's
        // derived code handles the missing-field case itself.
        visitor.visit_some(self)
    }

    fn deserialize_newtype_struct<V: serde::de::Visitor<'de>>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Error> {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_struct<V: serde::de::Visitor<'de>>(
        self,
        name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Error> {
        if name == DATETIME_PRIVATE_NAME {
            let (line, column) = self.position();
            return match self.item.kind {
                Kind::Datetime(value) => Self::deserialize_datetime(value, visitor),
                other => Err(Error::at(
                    format!("invalid type: {}, expected a TOML datetime", other.type_name()),
                    line,
                    column,
                )),
            };
        }
        let (line, column) = self.position();
        // `unknown field` / `missing field` come from serde's derived visitor
        // with no position. The struct's own table is the best anchor
        // available, and it is better than none.
        self.deserialize_any(visitor).map_err(|error| error.with_position(line, column))
    }

    fn deserialize_enum<V: serde::de::Visitor<'de>>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Error> {
        let (line, column) = self.position();
        let result = match self.item.kind {
            // `kind = "alpha"` — a unit variant. serde supplies the
            // `EnumAccess` for a plain string.
            Kind::String(variant) => visitor.visit_enum(variant.into_deserializer()),
            // `kind = { alpha = ... }` — a data variant, encoded the way the
            // incumbent encodes it: exactly one key, which names the variant.
            Kind::Table(table) if table.len() == 1 => {
                let (variant, value) =
                    table.into_iter().next().expect("length checked immediately above");
                visitor.visit_enum(TableEnumAccess { variant, value })
            }
            Kind::Table(table) => Err(Error::at(
                format!(
                    "expected a table with exactly one key naming the variant, found {} keys",
                    table.len()
                ),
                line,
                column,
            )),
            other => Err(Error::at(
                format!("invalid type: {}, expected a string or a table", other.type_name()),
                line,
                column,
            )),
        };
        result.map_err(|error| error.with_position(line, column))
    }

    // Everything else is genuinely `deserialize_any`. See the module docs for
    // why that is a decision and not laziness.
    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf unit unit_struct seq tuple tuple_struct map identifier
        ignored_any
    }
}

// ---------------------------------------------------------------------------
// accessors
// ---------------------------------------------------------------------------

struct TableMapAccess {
    iter: <Map<String, Item> as IntoIterator>::IntoIter,
    /// The entry whose key was just handed out. serde always calls
    /// `next_value_seed` immediately after a successful `next_key_seed`, and
    /// this is where the value waits in between.
    pending: Option<(String, Item)>,
}

impl<'de> serde::de::MapAccess<'de> for TableMapAccess {
    type Error = Error;

    fn next_key_seed<K: serde::de::DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Error> {
        let Some((key, item)) = self.iter.next() else {
            return Ok(None);
        };
        let (line, column) = (item.line, item.column);
        let name = key.clone();
        self.pending = Some((key, item));
        // A failure here is `unknown field` under `deny_unknown_fields`, which
        // is 116 containers in this tree. Naming the key and the line turns
        // that from a puzzle into a fix.
        seed.deserialize(name.clone().into_deserializer())
            .map(Some)
            .map_err(|error: Error| error.with_key(&name).with_position(line, column))
    }

    fn next_value_seed<V: serde::de::DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, Error> {
        let (key, item) =
            self.pending.take().expect("serde calls next_value_seed only after next_key_seed");
        let (line, column) = (item.line, item.column);
        seed.deserialize(ItemDeserializer::new(item))
            .map_err(|error| error.with_key(&key).with_position(line, column))
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.iter.len())
    }
}

struct ArraySeqAccess {
    iter: std::vec::IntoIter<Item>,
}

impl<'de> serde::de::SeqAccess<'de> for ArraySeqAccess {
    type Error = Error;

    fn next_element_seed<T: serde::de::DeserializeSeed<'de>>(
        &mut self,
        seed: T,
    ) -> Result<Option<T::Value>, Error> {
        let Some(item) = self.iter.next() else {
            return Ok(None);
        };
        let (line, column) = (item.line, item.column);
        seed.deserialize(ItemDeserializer::new(item))
            .map(Some)
            .map_err(|error| error.with_position(line, column))
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.iter.len())
    }
}

/// The reserved one-entry map that carries a datetime through serde's data
/// model. See `crate::datetime`.
struct DatetimeMapAccess {
    value: Option<String>,
}

impl<'de> serde::de::MapAccess<'de> for DatetimeMapAccess {
    type Error = Error;

    fn next_key_seed<K: serde::de::DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Error> {
        if self.value.is_none() {
            return Ok(None);
        }
        seed.deserialize(DATETIME_PRIVATE_FIELD.into_deserializer()).map(Some)
    }

    fn next_value_seed<V: serde::de::DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, Error> {
        let text = self.value.take().expect("serde calls next_value_seed only after next_key_seed");
        seed.deserialize(text.into_deserializer())
    }

    fn size_hint(&self) -> Option<usize> {
        Some(usize::from(self.value.is_some()))
    }
}

/// `variant = <value>` as a single-key table.
struct TableEnumAccess {
    variant: String,
    value: Item,
}

impl<'de> serde::de::EnumAccess<'de> for TableEnumAccess {
    type Error = Error;
    type Variant = TableVariantAccess;

    fn variant_seed<V: serde::de::DeserializeSeed<'de>>(
        self,
        seed: V,
    ) -> Result<(V::Value, Self::Variant), Error> {
        let (line, column) = (self.value.line, self.value.column);
        let name = self.variant.clone();
        let variant = seed
            .deserialize(self.variant.into_deserializer())
            .map_err(|error: Error| error.with_key(&name).with_position(line, column))?;
        Ok((variant, TableVariantAccess { value: self.value }))
    }
}

struct TableVariantAccess {
    value: Item,
}

impl<'de> serde::de::VariantAccess<'de> for TableVariantAccess {
    type Error = Error;

    fn unit_variant(self) -> Result<(), Error> {
        // `variant = <something>` was written, but the variant carries no data.
        // The incumbent rejects this too; accepting it would silently discard
        // whatever the author wrote on the right-hand side.
        Err(Error::at(
            "expected a string naming a unit variant, found a table",
            self.value.line,
            self.value.column,
        ))
    }

    fn newtype_variant_seed<T: serde::de::DeserializeSeed<'de>>(
        self,
        seed: T,
    ) -> Result<T::Value, Error> {
        seed.deserialize(ItemDeserializer::new(self.value))
    }

    fn tuple_variant<V: serde::de::Visitor<'de>>(
        self,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Error> {
        serde::Deserializer::deserialize_seq(ItemDeserializer::new(self.value), visitor)
    }

    fn struct_variant<V: serde::de::Visitor<'de>>(
        self,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Error> {
        serde::Deserializer::deserialize_map(ItemDeserializer::new(self.value), visitor)
    }
}
