// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The write path**: `to_string` / `to_string_pretty`, and the
//! [`serde::Serializer`] behind them.
//!
//! # Why the write path is the harder half
//!
//! A reader that misunderstands a construct produces a different configuration,
//! which is bad. A *writer* that misunderstands one produces a document that is
//! still valid TOML and means something else — and it does so on the way *out*,
//! into a file that is then read back by something else entirely, so the defect
//! surfaces arbitrarily far from its cause. The two canonical instances are both
//! structural and both live in [`crate::emit`]: a scalar written after a
//! `[table]` header silently joins that table, and an unquoted `a.b` is a dotted
//! key meaning `{a: {b: …}}`.
//!
//! This module owns the other half of the problem — turning a `Serialize` value
//! into a tree at all — and with it every way the write path can *fail*.
//!
//! # Where correctness comes from
//!
//! Three separable gates, so a failure in one does not hide behind another:
//!
//! 1. **`tests/serialize_differential.rs`, across the implementation
//!    boundary.** For every document in the pinned corpus: read it with this
//!    crate, write it with this crate, read the result **with the incumbent**,
//!    and require the tree to equal what the incumbent read from the original.
//!    Re-reading with our own parser would be a symmetric-bug blind spot — a
//!    mis-escape paired with a matching mis-unescape round-trips perfectly and
//!    is still a corrupt file for every other reader. Only the incumbent's
//!    parser can see that class.
//! 2. **Byte-identity on the shapes this workspace actually writes.** The
//!    eleven `toml::to_string*` call sites in `crates/` all serialize plain
//!    ASCII ledgers; on those, the emitters agree byte for byte and a test
//!    asserts it. That is what makes [`crate::emit`]'s documented string-style
//!    deviation affordable rather than a licence to drift.
//! 3. **This module's own unit tests**, for the failure modes a differential
//!    cannot reach: what happens to a `None`, a `()`, a `u64` past `i64::MAX`.
//!    The corpus contains no such value, because no such value can be written.
//!
//! # Dependencies
//!
//! Still exactly one, and still `serde` as a trait ABI: this implements
//! [`serde::Serializer`] so consumers keep their `#[derive(Serialize)]` and
//! compile verbatim under a Cargo dependency rename. Nothing here derives
//! anything.

use std::fmt;

use serde::ser::{
    Serialize, SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant,
    SerializeTuple, SerializeTupleStruct, SerializeTupleVariant,
};

use crate::datetime::{DATETIME_PRIVATE_FIELD, DATETIME_PRIVATE_NAME};
use crate::emit::{Node, Style};

/// Serialize `value` as a TOML document.
///
/// Arrays are written on one line. See [`to_string_pretty`] for the multi-line
/// form.
///
/// # Errors
///
/// If `value` does not serialize to a TOML *table*, or contains something TOML
/// cannot represent. Every such error names the fix — see [`Error`].
pub fn to_string<T: Serialize + ?Sized>(value: &T) -> Result<String, Error> {
    render(value, Style::Compact)
}

/// Serialize `value` as a TOML document, breaking arrays of two or more
/// elements one per line.
///
/// Measured against the incumbent, that array formatting is the *only*
/// difference between the two functions: strings, tables, headers and arrays of
/// length 0 or 1 are identical.
///
/// # Errors
///
/// As [`to_string`].
pub fn to_string_pretty<T: Serialize + ?Sized>(value: &T) -> Result<String, Error> {
    render(value, Style::Pretty)
}

fn render<T: Serialize + ?Sized>(value: &T, style: Style) -> Result<String, Error> {
    match value.serialize(NodeSerializer)? {
        Some(Node::Table(entries)) => Ok(crate::emit::document(&entries, style)),
        Some(other) => Err(Error::new(format!(
            "a TOML document is a table, and this value serializes to a {}. Options: wrap it in a \
             struct or a map with one field, or serialize the containing type instead",
            describe(&other)
        ))),
        // `Option::None` at the very top. A table entry holding `None` is
        // skipped (see `TableBuilder`), but there is no key to skip here.
        None => Err(Error::new(
            "a TOML document is a table, and this value serializes to nothing (`Option::None`). \
             Options: serialize the `Some` payload directly, or serialize a struct that carries \
             this field with `#[serde(skip_serializing_if = \"Option::is_none\")]`",
        )),
    }
}

fn describe(node: &Node) -> &'static str {
    match node {
        Node::String(_) => "string",
        Node::Integer(_) => "integer",
        Node::Float(_) => "float",
        Node::Boolean(_) => "boolean",
        Node::Datetime(_) => "datetime",
        Node::Array(_) => "array",
        Node::Table(_) => "table",
    }
}

// ---------------------------------------------------------------------------
// error
// ---------------------------------------------------------------------------

/// An error produced while writing TOML — the type [`crate::ser::Error`] names.
///
/// # A separate type from [`crate::de::Error`], deliberately
///
/// The incumbent has two error types, one per direction, and consumers write
/// `impl From<toml::de::Error> for …` (`crates/trust-version/src/lib.rs:638`).
/// If the two directions shared one type here, a consumer that later added the
/// matching `From<toml::ser::Error>` would be writing a **duplicate impl** and
/// would not compile — a build break caused by nothing but our internal reuse.
///
/// # Every message carries the fix
///
/// A refusal that says only "unsupported" is a defect (DESIGN_PHILOSOPHY
/// principle 10). Serialization refusals here are all about a Rust value with no
/// TOML spelling, and in every case there is something concrete the author can
/// do — so each message names the options rather than the obstacle alone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    message: String,
}

impl Error {
    fn new(message: impl Into<String>) -> Self {
        Self { message: message.into() }
    }

    /// The message, without decoration.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

impl serde::ser::Error for Error {
    fn custom<T: fmt::Display>(message: T) -> Self {
        Self::new(message.to_string())
    }
}

// ---------------------------------------------------------------------------
// the serializer
// ---------------------------------------------------------------------------

/// `Ok` is `Option<Node>`, and the `None` is load-bearing.
///
/// `Option::None` has no TOML spelling — TOML has no null. The incumbent's
/// answer, which consumers already depend on, is that a **table entry** whose
/// value is `None` is omitted entirely, while a `None` anywhere else is an
/// error (measured against `toml 0.8.23`: a struct with `absent: Option<u32> =
/// None` emits no `absent` key at all). Threading `Option<Node>` out of every
/// serializer method is what lets the table builder see "this entry produced
/// nothing" and drop the key, while the array builder sees the same thing and
/// refuses — the two positions genuinely differ, and a single `Node` return
/// could not tell them apart without a sentinel variant leaking into the public
/// [`crate::Value`].
struct NodeSerializer;

type Produced = Result<Option<Node>, Error>;

/// The message for a Rust value with no TOML representation, carrying the fix.
fn unrepresentable(what: &str, options: &str) -> Error {
    Error::new(format!("{what} has no TOML representation. Options: {options}"))
}

fn integer(value: i128) -> Produced {
    i64::try_from(value).map(Node::Integer).map(Some).map_err(|_| {
        Error::new(format!(
            "the integer `{value}` does not fit TOML's only integer type, a signed 64-bit \
             integer. Options: serialize it as a string, or split it into two fields"
        ))
    })
}

impl serde::Serializer for NodeSerializer {
    type Ok = Option<Node>;
    type Error = Error;

    type SerializeSeq = SeqBuilder;
    type SerializeTuple = SeqBuilder;
    type SerializeTupleStruct = SeqBuilder;
    type SerializeTupleVariant = TupleVariantBuilder;
    type SerializeMap = TableBuilder;
    type SerializeStruct = StructBuilder;
    type SerializeStructVariant = StructVariantBuilder;

    fn serialize_bool(self, value: bool) -> Produced {
        Ok(Some(Node::Boolean(value)))
    }

    fn serialize_i8(self, value: i8) -> Produced {
        Ok(Some(Node::Integer(value.into())))
    }

    fn serialize_i16(self, value: i16) -> Produced {
        Ok(Some(Node::Integer(value.into())))
    }

    fn serialize_i32(self, value: i32) -> Produced {
        Ok(Some(Node::Integer(value.into())))
    }

    fn serialize_i64(self, value: i64) -> Produced {
        Ok(Some(Node::Integer(value)))
    }

    fn serialize_i128(self, value: i128) -> Produced {
        integer(value)
    }

    fn serialize_u8(self, value: u8) -> Produced {
        Ok(Some(Node::Integer(value.into())))
    }

    fn serialize_u16(self, value: u16) -> Produced {
        Ok(Some(Node::Integer(value.into())))
    }

    fn serialize_u32(self, value: u32) -> Produced {
        Ok(Some(Node::Integer(value.into())))
    }

    /// A `u64` above `i64::MAX` is refused rather than wrapped.
    ///
    /// TOML has exactly one integer type and it is signed 64-bit, so there is no
    /// spelling for such a value. Wrapping it would write a negative number and
    /// read back as one — a wrong answer with no diagnostic anywhere.
    fn serialize_u64(self, value: u64) -> Produced {
        integer(value.into())
    }

    fn serialize_u128(self, value: u128) -> Produced {
        integer(i128::try_from(value).unwrap_or(i128::MAX))
    }

    /// Widened to `f64`, which is TOML's only float type.
    ///
    /// The widening is exact, but the *rendering* is of the widened value: `0.1f32`
    /// writes as `0.10000000149011612`, because that is the `f64` nearest to it.
    /// The incumbent does the same. Reading it back into an `f32` field narrows
    /// to the original `0.1f32`, so a round trip through a matching type is
    /// lossless; a round trip through `f64` is not, and cannot be.
    fn serialize_f32(self, value: f32) -> Produced {
        Ok(Some(Node::Float(value.into())))
    }

    fn serialize_f64(self, value: f64) -> Produced {
        Ok(Some(Node::Float(value)))
    }

    fn serialize_char(self, value: char) -> Produced {
        Ok(Some(Node::String(value.to_string())))
    }

    fn serialize_str(self, value: &str) -> Produced {
        Ok(Some(Node::String(value.to_string())))
    }

    /// An array of integers — which is what the incumbent writes.
    ///
    /// FOUND BY THE ADVERSARIAL DIFFERENTIAL. This used to return an error
    /// suggesting "serialize it as an array of integers", which is exactly what
    /// `toml 0.8` already does silently, so the refusal was a capability the
    /// rename would have taken away at *run* time: `to_string` on a
    /// `#[serde(with = "serde_bytes")]` field returns `Ok("a = [104, 105]\n")`
    /// today and would have started returning `Err`.
    ///
    /// It round-trips: `deserialize_bytes` forwards to `deserialize_any`
    /// (`src/deserializer.rs:180`), an array reaches the visitor as `visit_seq`,
    /// and that is the arm `serde_bytes`' visitor implements. Asserted in
    /// `tests/adversarial.rs` rather than argued — an emitter whose output
    /// nothing can read is the defect this same run found in the key path
    /// below.
    fn serialize_bytes(self, value: &[u8]) -> Produced {
        Ok(Some(Node::Array(
            value.iter().map(|byte| Node::Integer(i64::from(*byte))).collect(),
        )))
    }

    fn serialize_none(self) -> Produced {
        // Not an error here: the caller decides. A table entry drops the key; an
        // array element refuses. See `NodeSerializer`'s docs.
        Ok(None)
    }

    /// `Some(x)` is `x` — except when `x` is itself `None`.
    ///
    /// FOUND BY THE ADVERSARIAL DIFFERENTIAL, in the silent direction. A plain
    /// forward makes `Option<Option<T>>` collapse: `Some(None)` produces
    /// nothing, the key is dropped, and re-reading the document yields `None` —
    /// measured, both implementations re-read the emitted text as
    /// `a: None`. The two states `Option<Option<T>>` exists to distinguish
    /// become one, `to_string` reports success, and nothing anywhere fails.
    ///
    /// The incumbent refuses it (`unsupported None value`) and that is the
    /// right answer: TOML has no null, so a present-but-null field has no
    /// spelling. A refusal that names the fix is a supported outcome; a silent
    /// collapse is not.
    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Produced {
        match value.serialize(self)? {
            Some(node) => Ok(Some(node)),
            None => Err(Error::new(
                "a `Some` holding `None` — a present field with a null value — has no TOML \
                 representation, because TOML has no null. Writing nothing would erase the \
                 difference between `Some(None)` and `None`. Options: flatten the type to a \
                 single `Option`, or give the inner `None` a sentinel value",
            )),
        }
    }

    fn serialize_unit(self) -> Produced {
        Err(unrepresentable(
            "the unit value `()`",
            "remove the field, or give it a real value — TOML has no null and no empty scalar",
        ))
    }

    fn serialize_unit_struct(self, name: &'static str) -> Produced {
        Err(unrepresentable(
            &format!("the unit struct `{name}`"),
            "remove the field, or replace the type with one that carries data",
        ))
    }

    /// A fieldless enum variant is its name as a string — matching the
    /// incumbent, and matching how this crate *reads* one back.
    ///
    /// This is the shape every enum in this workspace's TOML ledgers uses
    /// (`status = "active"`, `head = "trustjs"`), by way of
    /// `#[serde(rename_all = "snake_case")]`.
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Produced {
        Ok(Some(Node::String(variant.to_string())))
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Produced {
        // Transparent, as everywhere else in serde.
        value.serialize(self)
    }

    /// A data-carrying variant becomes a one-entry table keyed by the variant
    /// name — serde's external tagging, which is what the incumbent emits
    /// (measured: `New(1)` becomes `[v]` / `New = 1`).
    ///
    /// **Not exercised by any consumer in this tree**, so it is not covered by
    /// the corpus differential; its evidence is the unit test
    /// `data_carrying_enum_variants_are_externally_tagged` and nothing else.
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        value: &T,
    ) -> Produced {
        let Some(inner) = value.serialize(NodeSerializer)? else {
            return Err(unrepresentable(
                &format!("the enum variant `{variant}` carrying `None`"),
                "give the variant a representable payload, or use a fieldless variant",
            ));
        };
        Ok(Some(Node::Table(vec![(variant.to_string(), inner)])))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<SeqBuilder, Error> {
        Ok(SeqBuilder { items: Vec::with_capacity(len.unwrap_or(0)) })
    }

    fn serialize_tuple(self, len: usize) -> Result<SeqBuilder, Error> {
        Ok(SeqBuilder { items: Vec::with_capacity(len) })
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<SeqBuilder, Error> {
        Ok(SeqBuilder { items: Vec::with_capacity(len) })
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<TupleVariantBuilder, Error> {
        Ok(TupleVariantBuilder {
            variant,
            items: SeqBuilder { items: Vec::with_capacity(len) },
        })
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<TableBuilder, Error> {
        Ok(TableBuilder::default())
    }

    fn serialize_struct(
        self,
        name: &'static str,
        _len: usize,
    ) -> Result<StructBuilder, Error> {
        // The datetime interception. `serde` has no datetime type, so both this
        // crate and the incumbent smuggle one through as a struct with a
        // reserved name (see `crate::datetime`). Recognising the name here is
        // what makes a `Datetime` field — and a `Value::Datetime` — emit as a
        // bare `1979-05-27T07:32:00Z` rather than as a table holding a
        // `$__toml_private_datetime` string.
        Ok(if name == DATETIME_PRIVATE_NAME {
            StructBuilder::Datetime(None)
        } else {
            StructBuilder::Table(TableBuilder::default())
        })
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<StructVariantBuilder, Error> {
        Ok(StructVariantBuilder { variant, fields: TableBuilder::default() })
    }
}

// ---------------------------------------------------------------------------
// builders
// ---------------------------------------------------------------------------

/// Arrays, tuples and tuple structs.
struct SeqBuilder {
    items: Vec<Node>,
}

impl SeqBuilder {
    fn push<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
        let Some(node) = value.serialize(NodeSerializer)? else {
            // The other half of the `None` decision. A table entry drops its
            // key; an array cannot, because dropping an element would silently
            // shorten the array — a wrong answer that parses.
            return Err(unrepresentable(
                "an `Option::None` inside an array",
                "filter the `None`s out before serializing, or use a sentinel element — an array \
                 cannot omit an element the way a table omits a key",
            ));
        };
        self.items.push(node);
        Ok(())
    }
}

impl SerializeSeq for SeqBuilder {
    type Ok = Option<Node>;
    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
        self.push(value)
    }

    fn end(self) -> Produced {
        Ok(Some(Node::Array(self.items)))
    }
}

impl SerializeTuple for SeqBuilder {
    type Ok = Option<Node>;
    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
        self.push(value)
    }

    fn end(self) -> Produced {
        Ok(Some(Node::Array(self.items)))
    }
}

impl SerializeTupleStruct for SeqBuilder {
    type Ok = Option<Node>;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
        self.push(value)
    }

    fn end(self) -> Produced {
        Ok(Some(Node::Array(self.items)))
    }
}

/// `Variant(a, b)` — externally tagged, payload as an array.
struct TupleVariantBuilder {
    variant: &'static str,
    items: SeqBuilder,
}

impl SerializeTupleVariant for TupleVariantBuilder {
    type Ok = Option<Node>;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
        self.items.push(value)
    }

    fn end(self) -> Produced {
        Ok(Some(Node::Table(vec![(
            self.variant.to_string(),
            Node::Array(self.items.items),
        )])))
    }
}

/// Maps and structs: an **ordered** table.
///
/// Order is `serde`'s presentation order, which for a struct is declaration
/// order. See [`crate::emit::Node`] for why that is worth carrying rather than
/// sorting.
#[derive(Default)]
struct TableBuilder {
    entries: Vec<(String, Node)>,
    pending_key: Option<String>,
}

impl TableBuilder {
    /// Insert, replacing a duplicate **in place**.
    ///
    /// A duplicate key can arise from a `HashMap<String, _>` with two keys that
    /// serialize alike, or a `#[serde(rename)]` collision. Appending would emit
    /// the key twice, which is not valid TOML; replacing in place matches
    /// last-write-wins on the value while keeping the first position, which is
    /// what an insertion-ordered map does.
    fn insert(&mut self, key: String, node: Node) {
        if let Some(slot) = self.entries.iter_mut().find(|(existing, _)| *existing == key) {
            slot.1 = node;
        } else {
            self.entries.push((key, node));
        }
    }

    fn set<T: Serialize + ?Sized>(&mut self, key: String, value: &T) -> Result<(), Error> {
        // `None` drops the key. This is the incumbent's behaviour and consumers
        // depend on it — `#[serde(skip_serializing_if = "Option::is_none")]` is
        // the usual spelling, but a plain `Option` field must not emit a key
        // with no value, because TOML has no way to write one.
        if let Some(node) = value.serialize(NodeSerializer)? {
            self.insert(key, node);
        }
        Ok(())
    }
}

impl SerializeMap for TableBuilder {
    type Ok = Option<Node>;
    type Error = Error;

    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<(), Error> {
        self.pending_key = Some(key.serialize(KeySerializer)?);
        Ok(())
    }

    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
        let key = self.pending_key.take().ok_or_else(|| {
            Error::new("a map value was serialized before its key (this is a `serde` protocol \
                        violation in the caller's `Serialize` impl)")
        })?;
        self.set(key, value)
    }

    fn end(self) -> Produced {
        Ok(Some(Node::Table(self.entries)))
    }
}

/// Structs — and the datetime smuggled through as one.
enum StructBuilder {
    Table(TableBuilder),
    /// Collecting the reserved datetime field; `None` until it arrives.
    Datetime(Option<String>),
}

impl SerializeStruct for StructBuilder {
    type Ok = Option<Node>;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        match self {
            Self::Table(table) => table.set(key.to_string(), value),
            Self::Datetime(slot) => {
                if key != DATETIME_PRIVATE_FIELD {
                    return Err(Error::new(format!(
                        "a value using the reserved datetime struct name carried the field \
                         `{key}` instead of `{DATETIME_PRIVATE_FIELD}`. Options: do not name a \
                         struct `{DATETIME_PRIVATE_NAME}` — that name is reserved for the \
                         serde-level datetime encoding"
                    )));
                }
                match value.serialize(NodeSerializer)? {
                    Some(Node::String(text)) => {
                        *slot = Some(text);
                        Ok(())
                    }
                    other => Err(Error::new(format!(
                        "the reserved datetime field carried a {} rather than its canonical text",
                        other.as_ref().map_or("nothing", describe)
                    ))),
                }
            }
        }
    }

    fn skip_field(&mut self, _key: &'static str) -> Result<(), Error> {
        Ok(())
    }

    fn end(self) -> Produced {
        match self {
            Self::Table(table) => Ok(Some(Node::Table(table.entries))),
            Self::Datetime(Some(text)) => Ok(Some(Node::Datetime(text))),
            Self::Datetime(None) => Err(Error::new(
                "a datetime serialized without its canonical text. Options: construct the \
                 `Datetime` through this crate rather than by hand",
            )),
        }
    }
}

/// `Variant { .. }` — externally tagged, payload as a table.
struct StructVariantBuilder {
    variant: &'static str,
    fields: TableBuilder,
}

impl SerializeStructVariant for StructVariantBuilder {
    type Ok = Option<Node>;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.fields.set(key.to_string(), value)
    }

    fn end(self) -> Produced {
        Ok(Some(Node::Table(vec![(
            self.variant.to_string(),
            Node::Table(self.fields.entries),
        )])))
    }
}

// ---------------------------------------------------------------------------
// map keys
// ---------------------------------------------------------------------------

/// Every TOML key is a string, so a map key must serialize to one — and
/// **only** a string does.
///
/// # The premise this used to carry, and the measurement that broke it
///
/// This type used to stringify integers, chars and booleans, on the stated
/// grounds that "a `BTreeMap<u32, _>` is an ordinary thing to serialize, and
/// `1 = "x"` is a legal TOML key". Both halves of that are true and the
/// conclusion is still wrong, because the sentence never mentions reading. The
/// adversarial differential measured the round trip:
///
/// ```text
///   to_string(&BTreeMap::from([(1i32, 2i32)]))  ->  Ok("1 = 2\n")
///   from_str::<BTreeMap<i32, i32>>("1 = 2\n")   ->  Err: invalid type: string "1", expected i32
/// ```
///
/// and the same for `bool` (`true = 2`) and `char` (`a = 2`) — with the
/// incumbent's reader too, not just ours. `to_string` reported success and
/// produced a document that **no reader can turn back into the type that wrote
/// it**. The incumbent refuses at write time (`map key was not a string`),
/// which is the fail-closed answer, so this now does too.
///
/// The general shape is worth naming: a permissive branch justified by a
/// comment about the write side alone. The comment was never false; it was
/// never tested against the other direction.
struct KeySerializer;

fn not_a_key(what: &str) -> Error {
    Error::new(format!(
        "{what} cannot be a TOML key — every key is a string. Options: give the key type a \
         `Serialize` impl that produces a string (`#[serde(with = \"…\")]`), or restructure the \
         map as an array of tables with the key as a field"
    ))
}

/// Every scalar that is not a string. Refused, one arm each, so that adding a
/// serde method cannot silently acquire a stringifying default — see
/// [`KeySerializer`] for the measurement that made these refusals.
macro_rules! key_refused {
    ($($method:ident($ty:ty) => $what:expr),* $(,)?) => {
        $(fn $method(self, _value: $ty) -> Result<String, Error> {
            Err(not_a_key($what))
        })*
    };
}

impl serde::Serializer for KeySerializer {
    type Ok = String;
    type Error = Error;

    type SerializeSeq = serde::ser::Impossible<String, Error>;
    type SerializeTuple = serde::ser::Impossible<String, Error>;
    type SerializeTupleStruct = serde::ser::Impossible<String, Error>;
    type SerializeTupleVariant = serde::ser::Impossible<String, Error>;
    type SerializeMap = serde::ser::Impossible<String, Error>;
    type SerializeStruct = serde::ser::Impossible<String, Error>;
    type SerializeStructVariant = serde::ser::Impossible<String, Error>;

    /// The only accepted key shape.
    fn serialize_str(self, value: &str) -> Result<String, Error> {
        Ok(value.to_string())
    }

    key_refused! {
        serialize_bool(bool) => "a boolean",
        serialize_i8(i8) => "an integer", serialize_i16(i16) => "an integer",
        serialize_i32(i32) => "an integer", serialize_i64(i64) => "an integer",
        serialize_i128(i128) => "an integer",
        serialize_u8(u8) => "an integer", serialize_u16(u16) => "an integer",
        serialize_u32(u32) => "an integer", serialize_u64(u64) => "an integer",
        serialize_u128(u128) => "an integer",
        serialize_char(char) => "a character",
        serialize_f32(f32) => "a float", serialize_f64(f64) => "a float",
    }

    fn serialize_bytes(self, _value: &[u8]) -> Result<String, Error> {
        Err(not_a_key("a byte string"))
    }

    fn serialize_none(self) -> Result<String, Error> {
        Err(not_a_key("`Option::None`"))
    }

    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<String, Error> {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<String, Error> {
        Err(not_a_key("the unit value `()`"))
    }

    fn serialize_unit_struct(self, name: &'static str) -> Result<String, Error> {
        Err(not_a_key(&format!("the unit struct `{name}`")))
    }

    /// A fieldless enum used as a map key is its variant name — the idiomatic
    /// spelling for a `BTreeMap<SomeEnum, _>`, and it round-trips.
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<String, Error> {
        Ok(variant.to_string())
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<String, Error> {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _value: &T,
    ) -> Result<String, Error> {
        Err(not_a_key(&format!("the data-carrying enum variant `{variant}`")))
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Error> {
        Err(not_a_key("an array"))
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Error> {
        Err(not_a_key("a tuple"))
    }

    fn serialize_tuple_struct(
        self,
        name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Error> {
        Err(not_a_key(&format!("the tuple struct `{name}`")))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Error> {
        Err(not_a_key(&format!("the enum variant `{variant}`")))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Error> {
        Err(not_a_key("a map"))
    }

    fn serialize_struct(
        self,
        name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Error> {
        Err(not_a_key(&format!("the struct `{name}`")))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Error> {
        Err(not_a_key(&format!("the enum variant `{variant}`")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Datetime, Table, Value};

    /// A hand-built `Serialize` impl, so these tests do not need `serde_derive`
    /// in the shipping dependency list. The dev-dependency has `derive`, but the
    /// unit tests compile against the shipping feature set.
    struct Fields<'a>(&'a [(&'a str, FieldValue<'a>)]);

    enum FieldValue<'a> {
        Int(i64),
        Str(&'a str),
        Opt(Option<i64>),
        List(&'a [i64]),
        Unit,
        Bytes(&'a [u8]),
        Big(u64),
    }

    impl Serialize for Fields<'_> {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            let mut map = serializer.serialize_map(Some(self.0.len()))?;
            for (key, value) in self.0 {
                match value {
                    FieldValue::Int(v) => map.serialize_entry(key, v)?,
                    FieldValue::Str(v) => map.serialize_entry(key, v)?,
                    FieldValue::Opt(v) => map.serialize_entry(key, v)?,
                    FieldValue::List(v) => map.serialize_entry(key, v)?,
                    FieldValue::Unit => map.serialize_entry(key, &())?,
                    FieldValue::Bytes(v) => {
                        map.serialize_entry(key, &serde_bytes_shim::Bytes(v))?;
                    }
                    FieldValue::Big(v) => map.serialize_entry(key, v)?,
                }
            }
            map.end()
        }
    }

    /// Reaching `serialize_bytes` needs a type that calls it; `&[u8]` does not
    /// (serde treats it as a sequence).
    mod serde_bytes_shim {
        pub struct Bytes<'a>(pub &'a [u8]);

        impl serde::Serialize for Bytes<'_> {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                serializer.serialize_bytes(self.0)
            }
        }
    }

    #[test]
    fn a_none_table_entry_drops_its_key_but_a_none_array_element_is_refused() {
        // The incumbent's behaviour, and the reason `Ok` is `Option<Node>`.
        let document = to_string(&Fields(&[
            ("present", FieldValue::Opt(Some(1))),
            ("absent", FieldValue::Opt(None)),
            ("after", FieldValue::Int(2)),
        ]))
        .expect("a dropped key is not an error");
        assert_eq!(document, "present = 1\nafter = 2\n");

        let error = to_string(&Fields(&[("k", FieldValue::List(&[]))]));
        assert!(error.is_ok(), "an empty array is fine");
        // An array of `Option` with a `None` in it.
        let error = to_string(&vec![Some(1), None])
            .expect_err("a None inside an array cannot be dropped");
        assert!(error.message().contains("inside an array"), "{error}");
        assert!(error.message().contains("Options:"), "every refusal names the fix: {error}");
    }

    #[test]
    fn the_root_must_be_a_table_and_the_refusal_says_so() {
        let error = to_string(&42_u32).expect_err("a bare integer is not a document");
        assert!(error.message().contains("a TOML document is a table"), "{error}");
        assert!(error.message().contains("integer"), "the refusal names what it got: {error}");
        assert!(error.message().contains("Options:"), "{error}");

        let error = to_string(&Option::<u32>::None).expect_err("`None` is not a document");
        assert!(error.message().contains("Options:"), "{error}");
    }

    #[test]
    fn values_with_no_toml_spelling_are_refused_with_the_fix_named() {
        for value in [FieldValue::Unit, FieldValue::Big(u64::MAX)] {
            let error =
                to_string(&Fields(&[("k", value)])).expect_err("no TOML spelling exists");
            assert!(
                error.message().contains("Options:"),
                "a refusal with no next step is a defect: {error}"
            );
        }
        // And the integer refusal names the actual limit rather than "invalid".
        let error = to_string(&Fields(&[("k", FieldValue::Big(u64::MAX))])).unwrap_err();
        assert!(error.message().contains("signed 64-bit"), "{error}");
    }

    /// Bytes DO have a TOML spelling, and this test used to assert they did
    /// not. The incumbent writes an array of integers; refusing was a
    /// capability the rename would have removed at run time. See
    /// `NodeSerializer::serialize_bytes`.
    #[test]
    fn a_byte_string_is_written_as_an_array_of_integers_and_reads_back() {
        let document = to_string(&Fields(&[("k", FieldValue::Bytes(&[1, 2]))])).unwrap();
        assert_eq!(document, "k = [1, 2]\n");
        let reread: Value = crate::from_str(&document).unwrap();
        assert_eq!(
            reread["k"].as_array().map(|items| items.len()),
            Some(2),
            "the emitted array is readable"
        );
    }

    #[test]
    fn struct_field_order_survives_and_is_not_sorted() {
        // The reason the intermediate is an ordered `Vec` and not a `Map`. A
        // sorted intermediate would emit `a` before `z` here.
        let document = to_string(&Fields(&[
            ("z", FieldValue::Int(1)),
            ("a", FieldValue::Int(2)),
        ]))
        .unwrap();
        assert_eq!(document, "z = 1\na = 2\n");
    }

    #[test]
    fn a_value_round_trips_and_comes_out_key_sorted() {
        // `Value`'s own map IS sorted, so this is the one input whose output is
        // alphabetical — matching the incumbent, whose `Value` is also sorted.
        let source = "z = 1\na = 2\n\n[t]\nk = \"v\"\n";
        let value: Value = crate::from_str(source).unwrap();
        assert_eq!(to_string(&value).unwrap(), "a = 2\nz = 1\n\n[t]\nk = \"v\"\n");
    }

    #[test]
    fn a_datetime_is_emitted_bare_rather_than_as_its_reserved_map() {
        // Without the interception in `serialize_struct` this would emit
        // `[d]` / `"$__toml_private_datetime" = "…"`, which parses back as a
        // table. Silent, and wrong.
        let source = "d = 1979-05-27T07:32:00Z\nld = 1979-05-27\nlt = 07:32:00\n";
        let value: Value = crate::from_str(source).unwrap();
        assert_eq!(to_string(&value).unwrap(), "d = 1979-05-27T07:32:00Z\nld = 1979-05-27\nlt = 07:32:00\n");

        // And directly, not only through `Value`.
        let mut table = Table::new();
        table.insert(
            "d".to_string(),
            Value::Datetime(Datetime {
                date: Some(crate::Date { year: 1979, month: 5, day: 27 }),
                time: None,
                offset: None,
            }),
        );
        assert_eq!(to_string(&table).unwrap(), "d = 1979-05-27\n");
    }

    #[test]
    fn data_carrying_enum_variants_are_externally_tagged() {
        // Measured against the incumbent: `New(1)` emits `[v]` / `New = 1`.
        // Nothing in this workspace serializes such a variant, so this test is
        // the ONLY evidence for this arm — the corpus differential cannot see
        // it.
        struct Newtype;
        impl Serialize for Newtype {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.serialize_newtype_variant("E", 0, "New", &1_u32)
            }
        }
        struct Tuple;
        impl Serialize for Tuple {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                use serde::ser::SerializeTupleVariant as _;
                let mut v = s.serialize_tuple_variant("E", 0, "Tup", 2)?;
                v.serialize_field(&1_u32)?;
                v.serialize_field(&2_u32)?;
                v.end()
            }
        }
        struct Struct;
        impl Serialize for Struct {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                use serde::ser::SerializeStructVariant as _;
                let mut v = s.serialize_struct_variant("E", 0, "Stru", 1)?;
                v.serialize_field("x", &1_u32)?;
                v.end()
            }
        }
        struct Holder<T>(T);
        impl<T: Serialize> Serialize for Holder<T> {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                use serde::ser::SerializeMap as _;
                let mut m = s.serialize_map(Some(1))?;
                m.serialize_entry("v", &self.0)?;
                m.end()
            }
        }
        assert_eq!(to_string(&Holder(Newtype)).unwrap(), "[v]\nNew = 1\n");
        assert_eq!(to_string(&Holder(Tuple)).unwrap(), "[v]\nTup = [1, 2]\n");
        assert_eq!(to_string(&Holder(Struct)).unwrap(), "[v.Stru]\nx = 1\n");
    }

    #[test]
    fn a_duplicate_key_replaces_in_place_rather_than_emitting_the_key_twice() {
        // Two keys emitting the same TOML key would otherwise produce a
        // document that this crate — and every other TOML reader — rejects.
        let document =
            to_string(&Fields(&[("k", FieldValue::Int(1)), ("k", FieldValue::Int(2))])).unwrap();
        assert_eq!(document, "k = 2\n");
        assert!(crate::from_str::<Value>(&document).is_ok(), "and the result is readable");
    }

    #[test]
    fn a_map_key_that_is_not_a_string_is_refused_because_the_document_would_be_unreadable() {
        use std::collections::BTreeMap;

        // This test asserted the OPPOSITE until the adversarial differential
        // measured the round trip: it pinned `to_string(&BTreeMap<u32, _>)` to
        // `"1 = 10\n"` and never tried to read that back. Nothing else did
        // either, so a write-only emitter passed a suite that looked thorough.
        // See `KeySerializer`'s documentation for the measurement.
        for (label, error) in [
            ("integer", to_string(&BTreeMap::from([(1_u32, 10_u32)])).unwrap_err()),
            ("boolean", to_string(&BTreeMap::from([(true, 10_u32)])).unwrap_err()),
            ("character", to_string(&BTreeMap::from([('a', 10_u32)])).unwrap_err()),
            ("tuple", to_string(&BTreeMap::from([((1_u32, 2_u32), 3_u32)])).unwrap_err()),
        ] {
            assert!(
                error.message().contains("every key is a string"),
                "the {label} key refusal says why: {error}"
            );
            assert!(error.message().contains("Options:"), "and names the fix: {error}");
        }

        // A string key needing quotes is still quoted, or it would parse as a
        // dotted key. The refusals above are about the key's TYPE, not its text.
        assert_eq!(
            to_string(&BTreeMap::from([("a.b".to_string(), 1_u32)])).unwrap(),
            "\"a.b\" = 1\n"
        );
    }

    /// The write-then-read property the test above exists to protect, stated
    /// once over the shapes that used to violate it.
    #[test]
    fn nothing_this_crate_agrees_to_write_is_unreadable_by_the_type_that_wrote_it() {
        use std::collections::BTreeMap;

        let map = BTreeMap::from([("k".to_string(), 1_u32)]);
        let document = to_string(&map).unwrap();
        assert_eq!(crate::from_str::<BTreeMap<String, u32>>(&document).unwrap(), map);

        // And the counter-example, kept as a live control: were the integer-key
        // arm to come back, THIS is what it would produce.
        let text = "1 = 10\n";
        assert!(
            crate::from_str::<BTreeMap<u32, u32>>(text).is_err(),
            "a stringified integer key does not read back as an integer key — which is why \
             writing one is refused"
        );
    }

    #[test]
    fn pretty_differs_from_compact_only_in_arrays_of_two_or_more() {
        let value = Fields(&[("k", FieldValue::List(&[1, 2])), ("s", FieldValue::Str("x"))]);
        assert_eq!(to_string(&value).unwrap(), "k = [1, 2]\ns = \"x\"\n");
        assert_eq!(
            to_string_pretty(&value).unwrap(),
            "k = [\n    1,\n    2,\n]\ns = \"x\"\n"
        );
        let single = Fields(&[("k", FieldValue::List(&[1]))]);
        assert_eq!(to_string(&single).unwrap(), to_string_pretty(&single).unwrap());
    }

    #[test]
    fn everything_this_crate_emits_is_readable_by_this_crate() {
        // A cheap total check: the writer must not produce a document the
        // parser in the same crate rejects. It cannot catch a symmetric bug —
        // that is what the incumbent-side differential is for — but it catches
        // an outright malformed emission immediately.
        let source = "\
a = 1
b = \"two\"
c = [1, 2, 3]
d = 1979-05-27T07:32:00Z
e = 1.5
f = true
\"quoted.key\" = 1

[t]
x = 1

[[aot]]
y = 1

[aot.sub]
z = 1

[[aot]]
y = 2
";
        let value: Value = crate::from_str(source).unwrap();
        for style in [to_string as fn(&Value) -> _, to_string_pretty] {
            let emitted = style(&value).unwrap();
            let reparsed: Value = crate::from_str(&emitted)
                .unwrap_or_else(|error| panic!("emitted document does not parse: {error}\n{emitted}"));
            assert_eq!(reparsed, value);
        }
    }
}
