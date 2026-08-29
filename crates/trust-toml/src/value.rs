// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The dynamic TOML value, for callers that read a document without a schema.
//!
//! # Why this exists at all when `from_str::<T>` is the normal path
//!
//! Most consumers deserialize into their own struct and never touch [`Value`].
//! Four in this tree do not: they read a `Cargo.toml` and assert things about
//! it (`crates/trust-router/tests/manifest_feature_plumbing.rs`,
//! `crates/trust-bmc/src/verifier_api.rs:11267`), or they parse a single
//! dependency line and re-render it (`crates/trust-deps/src/lib.rs:1600`).
//! Those callers index by string, so the shape they need is a dynamic tree.
//!
//! # The API is the incumbent's, spelled the same way on purpose
//!
//! Variant names, accessor names and the `Index` behaviour are copied from
//! `toml 0.8` because the whole replacement mechanism is a Cargo dependency
//! rename — consumers keep writing `toml::Value::as_str` and must keep
//! compiling verbatim. Where this crate deviates it says so at the site; the
//! deviations in this module are:
//!
//! * **No `Display`, still, now that a serializer exists.** The incumbent's
//!   `Display for Value` writes a *value* in inline position — `1`, `"s"`,
//!   `{ a = 1 }` — which is a different spelling from the document form
//!   [`crate::to_string`] produces, and this crate has not measured it. Nothing
//!   in this tree calls it: the one caller that renders an inline value,
//!   `crates/trust-deps/src/lib.rs:1632`, hand-rolls its own
//!   `format_inline_toml_value` and does not go through `Display`. A `Display`
//!   that printed the *document* form would compile at every call site and
//!   silently emit something else, which is the failure this crate exists not to
//!   have — so the impl stays absent until a caller needs it and its exact
//!   spelling has been measured against the incumbent.
//! * **No `From` conversions and no `Value::try_into`.** Nothing in this tree
//!   uses them, and each is a place for a silent numeric or ordering
//!   difference to hide.

use std::fmt;
use std::ops;

use serde::Deserialize as _;

use crate::datetime::{DATETIME_PRIVATE_FIELD, Datetime};
use crate::map::Map;

/// A TOML array.
pub type Array = Vec<Value>;

/// A TOML table: the type `toml::Table` names.
pub type Table = Map<String, Value>;

/// A dynamically typed TOML value.
///
/// Not `Eq`, `Ord` or `Hash`, because [`Value::Float`] holds an `f64`. That
/// matches the incumbent, and it is not an oversight: a NaN inside a value tree
/// would make those impls lie.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A string.
    String(String),
    /// A 64-bit signed integer. TOML has exactly one integer type.
    Integer(i64),
    /// A 64-bit float.
    Float(f64),
    /// `true` or `false`.
    Boolean(bool),
    /// One of TOML's four date/time forms.
    Datetime(Datetime),
    /// An array. TOML permits mixed element types.
    Array(Array),
    /// A table.
    Table(Table),
}

impl Value {
    /// The noun this crate uses in diagnostics, and the one the incumbent uses.
    #[must_use]
    pub fn type_str(&self) -> &'static str {
        match self {
            Self::String(_) => "string",
            Self::Integer(_) => "integer",
            Self::Float(_) => "float",
            Self::Boolean(_) => "boolean",
            Self::Datetime(_) => "datetime",
            Self::Array(_) => "array",
            Self::Table(_) => "table",
        }
    }

    /// The string, if this is one.
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    /// The integer, if this is one.
    ///
    /// Deliberately does **not** convert a float that happens to be integral:
    /// `1.0` is not an integer in TOML, and a lenient accessor here would let a
    /// typo in a config file pass unnoticed.
    #[must_use]
    pub fn as_integer(&self) -> Option<i64> {
        match self {
            Self::Integer(value) => Some(*value),
            _ => None,
        }
    }

    /// The float, if this is one. See [`Self::as_integer`]: an integer is not
    /// widened here either.
    #[must_use]
    pub fn as_float(&self) -> Option<f64> {
        match self {
            Self::Float(value) => Some(*value),
            _ => None,
        }
    }

    /// The boolean, if this is one.
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Boolean(value) => Some(*value),
            _ => None,
        }
    }

    /// The datetime, if this is one.
    #[must_use]
    pub fn as_datetime(&self) -> Option<&Datetime> {
        match self {
            Self::Datetime(value) => Some(value),
            _ => None,
        }
    }

    /// The array, if this is one.
    #[must_use]
    pub fn as_array(&self) -> Option<&Array> {
        match self {
            Self::Array(value) => Some(value),
            _ => None,
        }
    }

    /// The array, mutable.
    #[must_use]
    pub fn as_array_mut(&mut self) -> Option<&mut Array> {
        match self {
            Self::Array(value) => Some(value),
            _ => None,
        }
    }

    /// The table, if this is one.
    #[must_use]
    pub fn as_table(&self) -> Option<&Table> {
        match self {
            Self::Table(value) => Some(value),
            _ => None,
        }
    }

    /// The table, mutable.
    #[must_use]
    pub fn as_table_mut(&mut self) -> Option<&mut Table> {
        match self {
            Self::Table(value) => Some(value),
            _ => None,
        }
    }

    /// Whether this is a string.
    #[must_use]
    pub fn is_str(&self) -> bool {
        self.as_str().is_some()
    }

    /// Whether this is an integer.
    #[must_use]
    pub fn is_integer(&self) -> bool {
        self.as_integer().is_some()
    }

    /// Whether this is a float.
    #[must_use]
    pub fn is_float(&self) -> bool {
        self.as_float().is_some()
    }

    /// Whether this is a boolean.
    #[must_use]
    pub fn is_bool(&self) -> bool {
        self.as_bool().is_some()
    }

    /// Whether this is a datetime.
    #[must_use]
    pub fn is_datetime(&self) -> bool {
        self.as_datetime().is_some()
    }

    /// Whether this is an array.
    #[must_use]
    pub fn is_array(&self) -> bool {
        self.as_array().is_some()
    }

    /// Whether this is a table.
    #[must_use]
    pub fn is_table(&self) -> bool {
        self.as_table().is_some()
    }

    /// Look up a table key or an array position, returning `None` rather than
    /// panicking. The non-panicking counterpart of [`ops::Index`].
    #[must_use]
    pub fn get<I: Index>(&self, index: I) -> Option<&Value> {
        index.index(self)
    }

    /// [`Self::get`], mutable.
    #[must_use]
    pub fn get_mut<I: Index>(&mut self, index: I) -> Option<&mut Value> {
        index.index_mut(self)
    }
}

/// Types usable as an index into a [`Value`]: `&str`, `String`, `usize`.
///
/// Sealed, as the incumbent's is. It exists so `value.get("k")` and
/// `value[0]` are one method each rather than four.
pub trait Index: sealed::Sealed {
    #[doc(hidden)]
    fn index<'v>(&self, value: &'v Value) -> Option<&'v Value>;
    #[doc(hidden)]
    fn index_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value>;
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for str {}
    impl Sealed for String {}
    impl Sealed for usize {}
    impl<T: ?Sized + Sealed> Sealed for &T {}
}

impl Index for str {
    fn index<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        value.as_table()?.get(self)
    }

    fn index_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        value.as_table_mut()?.get_mut(self)
    }
}

impl Index for String {
    fn index<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        self.as_str().index(value)
    }

    fn index_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        self.as_str().index_mut(value)
    }
}

impl Index for usize {
    fn index<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        value.as_array()?.get(*self)
    }

    fn index_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        value.as_array_mut()?.get_mut(*self)
    }
}

impl<T: ?Sized + Index> Index for &T {
    fn index<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        (**self).index(value)
    }

    fn index_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        (**self).index_mut(value)
    }
}

impl<I: Index> ops::Index<I> for Value {
    type Output = Value;

    /// # Panics
    ///
    /// If the index is absent or the value is not the right kind — matching the
    /// incumbent. Callers that must not panic use [`Value::get`].
    fn index(&self, index: I) -> &Value {
        index.index(self).expect("index not found in TOML value")
    }
}

impl<I: Index> ops::IndexMut<I> for Value {
    fn index_mut(&mut self, index: I) -> &mut Value {
        index.index_mut(self).expect("index not found in TOML value")
    }
}

impl std::str::FromStr for Value {
    type Err = crate::de::Error;

    /// Parse a whole TOML *document* into a `Value`.
    ///
    /// Exactly [`crate::from_str::<Value>`], under the name the incumbent gives
    /// it. It exists because `text.parse::<toml::Value>()` is a spelling
    /// consumers use — around fifteen sites in `targo-trust` — and under a Cargo
    /// dependency rename those have to keep compiling verbatim.
    ///
    /// Note what it is *not*: this parses a document, so `"1"` is a parse error
    /// (a bare integer is not a document), not `Value::Integer(1)`. That matches
    /// the incumbent, and it is the reason this is a one-line forward rather
    /// than a second entry point with its own grammar.
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        crate::from_str(input)
    }
}

// ---------------------------------------------------------------------------
// serde
// ---------------------------------------------------------------------------

impl serde::Serialize for Value {
    /// Serialize into whatever format the caller supplies.
    ///
    /// This crate ships no TOML *serializer* (slice 1 is the read path), so
    /// this impl is for the case where a `Value` is a field of something the
    /// caller writes out as JSON or the like. The datetime encoding is the
    /// reserved-map form documented in `crate::datetime`, so a `Value` round
    /// trips through any self-describing format.
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::{SerializeMap as _, SerializeSeq as _};
        match self {
            Self::String(value) => serializer.serialize_str(value),
            Self::Integer(value) => serializer.serialize_i64(*value),
            Self::Float(value) => serializer.serialize_f64(*value),
            Self::Boolean(value) => serializer.serialize_bool(*value),
            Self::Datetime(value) => value.serialize(serializer),
            Self::Array(values) => {
                let mut sequence = serializer.serialize_seq(Some(values.len()))?;
                for value in values {
                    sequence.serialize_element(value)?;
                }
                sequence.end()
            }
            Self::Table(table) => {
                let mut map = serializer.serialize_map(Some(table.len()))?;
                for (key, value) in table {
                    map.serialize_entry(key, value)?;
                }
                map.end()
            }
        }
    }
}

impl<'de> serde::Deserialize<'de> for Value {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(ValueVisitor)
    }
}

struct ValueVisitor;

impl<'de> serde::de::Visitor<'de> for ValueVisitor {
    type Value = Value;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("any valid TOML value")
    }

    fn visit_bool<E: serde::de::Error>(self, value: bool) -> Result<Value, E> {
        Ok(Value::Boolean(value))
    }

    fn visit_i64<E: serde::de::Error>(self, value: i64) -> Result<Value, E> {
        Ok(Value::Integer(value))
    }

    fn visit_u64<E: serde::de::Error>(self, value: u64) -> Result<Value, E> {
        // Reachable only when a `Value` is built from some other format; this
        // crate's own deserializer never emits `visit_u64`, because TOML
        // integers are `i64`. Fail loudly rather than wrapping.
        i64::try_from(value).map(Value::Integer).map_err(|_| {
            serde::de::Error::custom(format!("integer `{value}` does not fit a TOML integer"))
        })
    }

    fn visit_f64<E: serde::de::Error>(self, value: f64) -> Result<Value, E> {
        Ok(Value::Float(value))
    }

    fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Value, E> {
        Ok(Value::String(value.to_string()))
    }

    fn visit_string<E: serde::de::Error>(self, value: String) -> Result<Value, E> {
        Ok(Value::String(value))
    }

    fn visit_some<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Value, D::Error> {
        Value::deserialize(deserializer)
    }

    fn visit_newtype_struct<D: serde::Deserializer<'de>>(
        self,
        deserializer: D,
    ) -> Result<Value, D::Error> {
        Value::deserialize(deserializer)
    }

    fn visit_seq<A: serde::de::SeqAccess<'de>>(self, mut access: A) -> Result<Value, A::Error> {
        let mut values = Vec::with_capacity(access.size_hint().unwrap_or(0));
        while let Some(value) = access.next_element()? {
            values.push(value);
        }
        Ok(Value::Array(values))
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, mut access: A) -> Result<Value, A::Error> {
        let Some(first) = access.next_key::<String>()? else {
            return Ok(Value::Table(Table::new()));
        };
        // A datetime arrives as a one-entry map under the reserved key (see
        // `crate::datetime`). Recognising it here is what makes
        // `from_str::<Value>` produce `Value::Datetime` rather than a table
        // holding a `$__toml_private_datetime` string — which is exactly the
        // kind of silent shape difference this crate is meant not to have.
        if first == DATETIME_PRIVATE_FIELD {
            let text: String = access.next_value()?;
            let parsed = crate::datetime::parse(&text, 1, 1)
                .map_err(|error| serde::de::Error::custom(error.message()))?;
            return Ok(Value::Datetime(parsed));
        }
        let mut table = Table::new();
        table.insert(first, access.next_value()?);
        while let Some((key, value)) = access.next_entry::<String, Value>()? {
            table.insert(key, value);
        }
        Ok(Value::Table(table))
    }
}
