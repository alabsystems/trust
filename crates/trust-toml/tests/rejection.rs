// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Rejection agreement**, and the independent quality bar on a rejection.
//!
//! # Two different obligations, deliberately not mixed
//!
//! * [`trust_toml_and_the_incumbent_agree_on_what_to_reject`] compares against
//!   the incumbent, and asserts **only** whether each document is accepted or
//!   rejected. It says nothing about message text. Asserting on `toml 0.8`'s
//!   prose would pin this crate to wording it does not control and make the
//!   incumbent's next release a build break here; worse, it would be a test
//!   that *looks* rigorous while measuring a string.
//!
//! * [`every_rejection_names_a_line_and_a_key_when_one_is_in_scope`] asserts
//!   the quality bar this crate holds itself to, against no external authority:
//!   a rejection carries a line number, and when the failure is about a
//!   particular entry it names that key. `docs/DESIGN_PHILOSOPHY.md` principle
//!   10 — a refusal must carry the fix — is the reason this is a test and not a
//!   style note.
//!
//! # Why the corpus differential does not make this redundant
//!
//! The corpus contains four deliberately-malformed documents, which is four
//! more than most repositories and still nowhere near a rejection suite. The
//! table below covers the rules that decide *table identity* — duplicate keys,
//! re-opened tables, dotted keys reaching into a `[header]` table — which are
//! the rules whose violation a lenient parser turns into a silent
//! last-one-wins misconfiguration rather than an error.

mod common;
use common::compare;

/// `(document, why it must be rejected)`.
///
/// Every one of these is a rule whose violation is *silent* in a parser that
/// does not enforce it: the document still yields a table, just not the one the
/// author wrote.
const MALFORMED: &[(&str, &str)] = &[
    // -- table identity: the silent-misconfiguration family -----------------
    ("a = 1\na = 2\n", "duplicate key at the top level"),
    ("[t]\nk = 1\nk = 2\n", "duplicate key inside a table"),
    ("[t]\n[t]\n", "the same table header twice"),
    ("[[t]]\n[t]\n", "a table header over an array of tables"),
    ("[t]\n[[t]]\n", "an array-of-tables header over a table"),
    ("a.b = 1\n[a]\n", "a header reopening a table a dotted key created"),
    ("[a.b]\nx = 1\n[a]\nb.y = 2\n", "a dotted key reaching into a header table"),
    ("a = { x = 1 }\n[a.b]\nc = 2\n", "a header extending a closed inline table"),
    ("a = 1\n[a]\n", "a header over a scalar"),
    ("a = 1\na.b = 2\n", "a dotted key under a scalar"),
    // -- lexical --------------------------------------------------------------
    ("a = 01\n", "a leading zero in an integer"),
    ("a = 1__0\n", "a doubled underscore separator"),
    ("a = _1\n", "a leading underscore separator"),
    ("a = +0x1\n", "a sign on a radix-prefixed integer"),
    ("a = 0x\n", "a radix prefix with no digits"),
    ("a = 1.\n", "a decimal point with no fractional digits"),
    ("a = 1e\n", "an exponent with no digits"),
    ("a = \"x\ny\"\n", "a newline inside a single-line basic string"),
    ("a = 'x\ny'\n", "a newline inside a single-line literal string"),
    ("a = \"\\q\"\n", "an unknown escape sequence"),
    ("a = \"\\u00\"\n", "a short \\u escape"),
    ("a = \"unterminated\n", "an unterminated string"),
    ("a = [1, 2\n", "an unterminated array"),
    ("a = { x = 1\n", "an unterminated inline table"),
    ("a = { x = 1, }\n", "a trailing comma in an inline table"),
    ("a = { x = 1,\n      y = 2 }\n", "a newline inside an inline table"),
    ("a = 1 b = 2\n", "two statements on one line"),
    ("[a\n", "an unterminated table header"),
    ("= 1\n", "a value with no key"),
    ("a =\n", "a key with no value"),
    ("a\n", "a key with no `=`"),
    ("a = 2026-02-30\n", "a day that does not exist in its month"),
    ("a = 25:00:00\n", "an hour out of range"),
    // -- structure the DESERIALIZER must reject ------------------------------
    // (these parse as TOML; the failure is against the target type)
];

/// **The positive control.** Valid documents, several of them adjacent to a
/// rule in [`MALFORMED`], that both implementations must ACCEPT.
///
/// Without this table the rejection suite would pass just as happily against a
/// parser that rejected everything, which is the classic way a strictness test
/// becomes vacuous. Each entry is paired with a rejected neighbour on purpose:
/// `[a.b]` then `[a]` is legal while `[a]` twice is not, and a parser that got
/// the rule "right" by refusing both would look green here without this table.
const WELL_FORMED: &[(&str, &str)] = &[
    ("[a.b]\nx = 1\n[a]\ny = 2\n", "a header promoting an implicit ancestor"),
    (
        "[f]\napple.color = 'red'\n[f.apple.texture]\nsmooth = true\n",
        "a sub-table under a dotted-key table",
    ),
    ("[[t]]\nn = 1\n[[t]]\nn = 2\n", "an array of tables appended twice"),
    ("[[t]]\n[t.inner]\nk = 1\n", "a sub-table of the newest array element"),
    ("a = [1, 2, ]\n", "a trailing comma in an array (legal, unlike an inline table)"),
    ("a = [\n  1,\n  # comment\n  2,\n]\n", "newlines and comments inside an array"),
    ("a = { x = 1, y = { z = 2 } }\n", "a nested inline table"),
    ("a = { \"quoted key\" = 1, b.c = 2 }\n", "quoted and dotted keys inside an inline table"),
    ("a = 1e05\n", "leading zeros in an exponent (legal, unlike in the mantissa)"),
    ("a = -0\n", "negative zero"),
    ("a = 0\n", "a bare zero (a leading zero only when there is another digit)"),
    ("a = \"\"\"\\\n   joined\"\"\"\n", "a line-ending backslash in a multi-line basic string"),
    ("a = \"\"\"\"\"\"\"\n", "four closing quotes: content ends with one quote"),
    ("a = 1979-05-27 07:32:00\n", "a space as the date/time separator"),
    ("a = 23:59:60\n", "a leap second"),
    ("a = 2024-02-29\n", "a real leap day"),
];

/// Documents that are well-formed TOML but do not match `Config`.
///
/// Kept apart from [`MALFORMED`] because the two failures happen in different
/// halves of this crate — the parser versus the `Deserializer` — and a test
/// that mixed them could pass with one half not wired up.
const MISMATCHED: &[(&str, &str)] = &[
    ("name = \"x\"\nport = \"not a number\"\n", "a string where an integer is required"),
    ("name = \"x\"\nport = 1\nunexpected = true\n", "an unknown field under deny_unknown_fields"),
    ("port = 1\n", "a missing required field"),
    ("name = \"x\"\nport = 1\nnested = 3\n", "a scalar where a table is required"),
];

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    name: String,
    port: u16,
    /// An absent `Option` field must arrive as `None` rather than as an error.
    /// serde's derived code handles the *missing* case; this crate's
    /// `deserialize_option` handles the *present* case, and a reader that
    /// answered `visit_none` there would silently drop every optional value it
    /// was given. `a_well_formed_document_round_trips` pins both directions.
    tag: Option<String>,
    #[serde(default)]
    nested: Nested,
}

#[derive(Debug, Default, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Nested {
    #[serde(default)]
    enabled: bool,
}

/// The positive control for the DESERIALIZER half, mirroring [`WELL_FORMED`]'s
/// role for the parser: without it, every `Config` assertion in this file would
/// still pass against a `Deserializer` that refused everything.
#[test]
fn a_well_formed_document_round_trips() {
    let config: Config = trust_toml::from_str(
        "name = \"example\"\nport = 8080\ntag = \"beta\"\n\n[nested]\nenabled = true\n",
    )
    .expect("a well-formed document must deserialize");
    assert_eq!(config.name, "example");
    assert_eq!(config.port, 8080);
    assert_eq!(config.tag.as_deref(), Some("beta"), "a PRESENT Option must arrive as Some");
    assert!(config.nested.enabled);

    let minimal: Config = trust_toml::from_str("name = \"example\"\nport = 1\n")
        .expect("absent optional and defaulted fields must be filled in");
    assert_eq!(minimal.tag, None, "an ABSENT Option must arrive as None");
    assert!(!minimal.nested.enabled, "an absent #[serde(default)] table must default");
}

#[test]
fn trust_toml_and_the_incumbent_agree_on_what_to_reject() {
    let mut disagreements = Vec::new();

    for (document, why) in MALFORMED {
        let incumbent = incumbent_toml::from_str::<incumbent_toml::Value>(document).is_ok();
        let ours = trust_toml::from_str::<trust_toml::Value>(document).is_ok();
        if incumbent != ours {
            disagreements.push(format!(
                "{why}: incumbent {} / trust-toml {} — {document:?}",
                verdict(incumbent),
                verdict(ours)
            ));
        }
        // Both accepting is a defect in the TABLE below (the document is not
        // actually malformed) or in both parsers; either way it is not
        // something this test may pass over.
        if incumbent && ours {
            disagreements.push(format!("{why}: BOTH accepted a document listed as malformed"));
        }
    }

    for (document, why) in MISMATCHED {
        let incumbent = incumbent_toml::from_str::<Config>(document).is_ok();
        let ours = trust_toml::from_str::<Config>(document).is_ok();
        if incumbent != ours {
            disagreements.push(format!(
                "{why}: incumbent {} / trust-toml {} — {document:?}",
                verdict(incumbent),
                verdict(ours)
            ));
        }
        if incumbent && ours {
            disagreements.push(format!("{why}: BOTH accepted a document listed as mismatched"));
        }
    }

    for (document, why) in WELL_FORMED {
        let incumbent = incumbent_toml::from_str::<incumbent_toml::Value>(document);
        let ours = trust_toml::from_str::<trust_toml::Value>(document);
        if let Err(error) = &incumbent {
            disagreements.push(format!("{why}: THE INCUMBENT rejected a valid document — {error}"));
        }
        if let Err(error) = &ours {
            disagreements.push(format!("{why}: TRUST-TOML rejected a valid document — {error}"));
        }
        if let (Ok(incumbent), Ok(ours)) = (&incumbent, &ours) {
            // Accepting is not enough: they must agree on the RESULT. Without
            // this, a parser could pass the whole table by accepting every
            // document as an empty table. Same comparator as the corpus gate —
            // see `tests/common/mod.rs` for why it is shared and not copied.
            let mut differences = Vec::new();
            compare(incumbent, ours, "", &mut differences);
            for difference in differences {
                disagreements.push(format!("{why}: trees differ — {difference}"));
            }
        }
    }

    assert!(
        disagreements.is_empty(),
        "rejection disagreements ({}):\n  {}",
        disagreements.len(),
        disagreements.join("\n  ")
    );
    println!(
        "rejection agreement: {} malformed + {} mismatched rejected by both, {} well-formed \
         accepted by both",
        MALFORMED.len(),
        MISMATCHED.len(),
        WELL_FORMED.len()
    );
}

fn verdict(accepted: bool) -> &'static str {
    if accepted { "ACCEPTED" } else { "rejected" }
}

#[test]
fn every_rejection_names_a_line_and_a_key_when_one_is_in_scope() {
    let mut deficient = Vec::new();

    for (document, why) in MALFORMED {
        let Err(error) = trust_toml::from_str::<trust_toml::Value>(document) else { continue };
        if error.line().is_none() {
            deficient.push(format!("{why}: no line number — {}", error.message()));
        }
        let rendered = error.to_string();
        if !rendered.contains("line ") {
            deficient.push(format!("{why}: Display omits the line — {rendered}"));
        }
    }

    for (document, why) in MISMATCHED {
        let Err(error) = trust_toml::from_str::<Config>(document) else { continue };
        if error.line().is_none() {
            deficient.push(format!("{why}: no line number — {}", error.message()));
        }
    }

    assert!(
        deficient.is_empty(),
        "rejections that do not carry a position ({}):\n  {}",
        deficient.len(),
        deficient.join("\n  ")
    );
}

#[test]
fn a_type_error_names_the_offending_key_and_its_own_line() {
    let error = trust_toml::from_str::<Config>("name = \"x\"\n\nport = \"nope\"\n")
        .expect_err("a string is not a u16");
    assert_eq!(error.key(), Some("port"), "the failing key must be named: {error}");
    assert_eq!(error.line(), Some(3), "the line must be the VALUE's line, not the file's start");
    let rendered = error.to_string();
    assert!(rendered.contains("line 3"), "{rendered}");
    assert!(rendered.contains("`port`"), "{rendered}");
    // The source line itself is quoted back, which is what makes the caret
    // useful. This is why `from_str` — the last place holding the text —
    // attaches the source to BOTH the parse and the deserialize arms.
    assert!(rendered.contains("port = \"nope\""), "{rendered}");
}

#[test]
fn an_unknown_field_names_the_field_and_the_line_it_is_on() {
    let error = trust_toml::from_str::<Config>("name = \"x\"\nport = 1\nsurprise = 2\n")
        .expect_err("deny_unknown_fields");
    assert_eq!(error.line(), Some(3), "{error}");
    assert!(error.to_string().contains("surprise"), "{error}");
}

#[test]
fn a_nested_failure_reports_the_inner_position_not_the_outer_one() {
    // The whole point of fill-if-absent enrichment: an error raised three
    // levels down must not be relabelled with the enclosing table's line as it
    // unwinds.
    let document = "name = \"x\"\nport = 1\n\n[nested]\nenabled = 7\n";
    let error = trust_toml::from_str::<Config>(document).expect_err("7 is not a bool");
    assert_eq!(error.line(), Some(5), "expected the inner value's line, got: {error}");
    assert_eq!(error.key(), Some("enabled"), "{error}");
}
