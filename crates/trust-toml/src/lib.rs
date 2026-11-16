// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The Trust-owned TOML reader**, implementing **TOML v1.0.0**.
//!
//! # Why this crate exists
//!
//! Third-party compilation units report `dependency-policy-excluded` in the
//! verified lane: a proof about code that links them is conditional on units
//! Trust does not own. The replacement program retires them in phases ordered
//! by packages-killed-per-replacement, and `toml` is the largest single win
//! available to `crates/`. Measured on the 251-unit shipping closure — NORMAL
//! dependency-kind edges only, platform-filtered — replacing it takes the
//! third-party unit count from **121 to 115**, retiring `toml`, `toml_edit`,
//! `toml_datetime`, `toml_write`, `serde_spanned` and `winnow`.
//!
//! It is also the win that is fully *earned in this repository*. All five
//! in-closure parents of `toml` are `crates/` workspace members, so unlike the
//! `serde` stack — which is atomic across `crates/` and at least six
//! `first-party/*` repositories — nothing here is deferred behind a sibling.
//! (That asymmetry is the reason this crate exists before a `trust-serde`
//! does.)
//!
//! # What correctness means here, and how it is established
//!
//! A configuration reader fails *quietly*. It does not crash on a document it
//! misunderstands; it returns a different configuration, and the consumer's
//! `#[serde(default)]` fills the gap with something plausible. `a.b = 1` read
//! as a flat key named `"a.b"` is a green build and a wrong program. So the
//! evidence is layered, and each layer can fail independently:
//!
//! 1. **A differential against the incumbent over this repository's own
//!    corpus.** `tests/differential_corpus.rs` parses every file in a
//!    checked-in manifest — relative path plus SHA-256, so a corpus change is a
//!    visible diff rather than a silent sample shift — with both `toml 0.8` and
//!    this crate, and asserts that they accept and reject the same documents
//!    and, on acceptance, produce equal trees. This is the acceptance gate for
//!    the swap. It is a differential and not a fixture suite because the
//!    constructs an author forgets to write a fixture for are exactly the
//!    constructs that fail silently.
//! 2. **Rejection agreement.** `tests/rejection.rs` drives hand-written
//!    malformed documents through both implementations and asserts they agree
//!    on *whether* to reject. It deliberately does **not** assert on message
//!    text: over-fitting to another crate's prose pins us to wording we do not
//!    control. It asserts separately, and against no external authority, that
//!    every rejection names a line and — when one is in scope — a key.
//! 3. **Grammar units.** `src/parser.rs`'s own tests pin each construct
//!    measured to occur in the corpus, and the table-identity rules that a
//!    differential can only catch if the corpus happens to contain a violation.
//!
//! # Scope: both directions, as of slice 2
//!
//! Slice 1 shipped the read path. Slice 2 added the write path — [`to_string`],
//! [`to_string_pretty`] and the [`serde::Serializer`] behind them — because
//! without it the five `crates/` consumers of `toml` cannot all be renamed onto
//! this crate, and a rename that reaches four of five measures as a kill of
//! zero: the incumbent stays in the shipping closure for the fifth.
//!
//! The write path's acceptance gate is **not** byte-identity with the
//! incumbent's emitter, which is what slice 1's header predicted it would be.
//! That prediction was reconsidered and dropped: `toml 0.8` picks among four
//! string spellings by a private heuristic, and reproducing it exactly is
//! reverse engineering in service of a property nothing depends on. The gate is
//! a **round-trip differential across the implementation boundary** — our text,
//! re-read by the incumbent, must equal the tree the incumbent read from the
//! original — plus byte-identity on the shapes this workspace actually writes.
//! `crates/trust-toml/src/emit.rs` names every measured difference at its site.
//!
//! # Dependencies
//!
//! One: `serde`, as a **trait ABI**. This crate implements
//! [`serde::Deserializer`] so that every consumer keeps its existing
//! `#[derive(Deserialize)]` and compiles verbatim under a Cargo dependency
//! rename. It is not a data-format dependency, and it is not `serde_derive` —
//! this crate derives nothing. Notably there is no parser-combinator crate
//! either: `winnow` is one of the six units being retired.
//!
//! The example below is mirrored as an executable test —
//! `tests/consumer_surface.rs::the_crate_doc_example_is_true`. That is not
//! belt-and-braces: measured on this clone, the doctest lane cannot run at all
//! (host `rustdoc` hits an ABI skew, stage2 `trustdoc` verifies by default and
//! rejects the per-unit off-switch `targo` would supply). A doc example nobody
//! executes is an unverified claim; keep the two in step.
//!
//! ```
//! # fn main() -> Result<(), trust_toml::de::Error> {
//! let document = r#"
//! title = "example"
//!
//! [owner]
//! name = "Andrew"
//! ports = [8001, 8002]
//! "#;
//!
//! let value: trust_toml::Value = trust_toml::from_str(document)?;
//! assert_eq!(value["title"].as_str(), Some("example"));
//! assert_eq!(value["owner"]["name"].as_str(), Some("Andrew"));
//! assert_eq!(value["owner"]["ports"][1].as_integer(), Some(8002));
//! # Ok(())
//! # }
//! ```

#![forbid(unsafe_code)]

mod datetime;
/// The `Deserializer` implementation. Named `deserializer` rather than `de` so
/// the public `de` module below can carry the path the incumbent exposes.
mod deserializer;
mod emit;
mod error;
/// The table type.
///
/// Public because the incumbent's is: `crates/targo-trust`'s
/// `src/trust_added/stage0_lineage.rs:454` names `toml::map::Map` directly, and
/// under a dependency rename that path has to resolve here. [`Map`] is
/// re-exported at the crate root as well, which is how most callers reach it.
pub mod map;
mod parser;
pub mod ser;
mod value;

pub use crate::datetime::{Date, Datetime, Offset, Time};
pub use crate::map::Map;
pub use crate::ser::{to_string, to_string_pretty};
pub use crate::value::{Array, Index, Table, Value};

/// Deserialization: the error type, and `from_str` under the name the incumbent
/// gives it.
///
/// Consumers name `toml::de::Error` in `#[from]` attributes
/// (`crates/trust-upstream-compat/src/parse.rs:21`) and in manual `From` impls
/// (`crates/trust-version/src/lib.rs:638`), so the path has to exist exactly
/// here.
pub mod de {
    pub use super::from_str;
    pub use crate::error::Error;
}

/// Parse a TOML document into `T`.
///
/// # Errors
///
/// If the document is not well-formed TOML, or if it does not match `T`'s
/// shape. Either way the [`de::Error`] carries the line — and, when the failure
/// is about a particular entry, the key.
pub fn from_str<T: serde::de::DeserializeOwned>(input: &str) -> Result<T, de::Error> {
    // `attach_source` on both arms, not one: a *deserialization* failure is
    // just as entitled to show the offending line as a *parse* failure, and
    // this function is the last place that still holds the text.
    let document = parser::parse_document(input).map_err(|error| error.attach_source(input))?;
    T::deserialize(deserializer::ItemDeserializer::new(document))
        .map_err(|error| error.attach_source(input))
}
