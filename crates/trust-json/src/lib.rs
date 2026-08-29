// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # trust-json — the Trust-owned JSON data format
//!
//! A drop-in replacement for `serde_json`'s data model, writer and parser, with
//! **zero third-party dependencies**. Its acceptance criterion is not "emits
//! valid JSON": it is "emits the SAME BYTES", because this tree hashes
//! serialized JSON (`crates/trust-types/src/digest.rs`) and compares the
//! digests across processes and across release boundaries.
//!
//! ## What is already byte-checked against the incumbent
//!
//! `tests/differential_json.rs` runs both implementations and compares bytes:
//! several million random `f64`/`f32` bit patterns, an exhaustive `u16` string
//! sweep and a random Unicode string sweep, a random `Value` tree generator
//! through both the compact and the pretty writer, and a parse differential
//! over the same corpus plus an enumerated malformed-input table.
//!
//! ## SEAM: where the serde layer plugs in
//!
//! This crate deliberately does **not** depend on `serde`. The phase-2 plan
//! defers the serde replacement (it is atomic across six repositories); this
//! crate is useful before that lands and must not be blocked on it. The two
//! seams a serde layer attaches to are:
//!
//! * [`ser::Formatter`] — a transcription of `serde_json::ser::Formatter`, same
//!   method names and signatures over [`std::io::Write`]. A `Serializer`
//!   written against a serde-traits crate drives it exactly as `serde_json`'s
//!   does. Every decision about what bytes come out lives behind this trait, so
//!   the serde layer cannot accidentally re-decide one.
//! * [`Value`] / [`Number`] / [`Map`] — the tree a `Deserialize` impl builds
//!   into and a `Serialize` impl walks. [`de::Deserializer`] already produces
//!   it; wrapping that in a serde `Deserializer` is mechanical.
//!
//! Until then the free functions are monomorphic over `&Value` rather than
//! generic over `T: Serialize`. Their OUTPUT is what the gate measures, and
//! that does not change when the bound is generalised.
//!
//! ### One constraint the serde layer MUST honour, measured
//!
//! A derived struct and a `Value::Object` do **not** order their keys the same
//! way, and both orders are load-bearing:
//!
//! ```text
//! #[derive(Serialize)] struct S { z: u8, a: u8, m: u8 }
//! serde_json::to_string(&S { z:1, a:2, m:3 })  ->  {"z":1,"a":2,"m":3}   DECLARATION order
//! serde_json::to_string(&json!({"z":1,"a":2,"m":3}))  ->  {"a":2,"m":3,"z":1}   SORTED
//! ```
//!
//! So a `Serialize` impl for a struct must drive [`ser::Formatter`]'s
//! `begin_object_key` / `begin_object_value` **directly, field by field**. It
//! must NOT build a [`Map`] and serialize that — the map is sorted, and doing
//! so would silently re-order every derived struct in the tree and change every
//! digest. The `Formatter` seam is shaped to make the correct thing the easy
//! thing; this note exists because the wrong thing also compiles.
//!
//! ## Known differences from the incumbent, stated rather than discovered
//!
//! * `json!` interpolates `Into<Value>`, not `Serialize` — see [`macros`].
//! * `from_slice` on input that is not valid UTF-8 reports
//!   `invalid unicode code point` at the position where the parser copied the
//!   bad bytes, which need not be the incumbent's byte offset. Every caller in
//!   this tree feeds it either a `&str` or bytes that came from one.
//! * `arbitrary_precision`, `raw_value`, `preserve_order` and `float_roundtrip`
//!   have no counterpart, on purpose: measured across `crates/` and
//!   `targo-trust/`, exactly one non-default feature is enabled anywhere
//!   (`unbounded_depth`), which is [`de::Deserializer::disable_recursion_limit`].

#![forbid(unsafe_code)]

pub mod de;
pub mod error;
pub mod macros;
pub mod map;
pub mod number;
pub mod ser;
pub mod value;

pub use crate::de::{Deserializer, from_slice, from_str};
pub use crate::error::{Category, Error, Result};
pub use crate::map::Map;
pub use crate::number::Number;
pub use crate::ser::{
    CharEscape, CompactFormatter, Formatter, PrettyFormatter, to_string, to_string_pretty, to_vec,
    to_vec_pretty, to_writer, to_writer_pretty,
};
pub use crate::value::Value;
