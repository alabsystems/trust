// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The adversarial gate.** Hand-enumerated hazards, not a corpus.
//!
//! The corpus differential (`differential_corpus.rs`) and the write-path
//! differential (`serialize_differential.rs`) both measure this repository's
//! own TOML. That is the right acceptance gate for the swap and it is
//! structurally blind to every construct this repository does not happen to
//! write. Measured while building this file: exactly **one** of 1381 corpus
//! documents contains a float, **none** contains a datetime with an offset,
//! **none** contains `\u` escapes, and **none** contains an integer within
//! twelve orders of magnitude of `i64::MAX`. Size is not coverage.
//!
//! So this file enumerates hazards by hand, in four families:
//!
//! 1. **Read path** — every case is run through BOTH implementations and must
//!    agree on accept/reject and, on accept, on the tree.
//! 2. **Write path** — a `Value` built identically on both sides, emitted by
//!    both, compared BYTE for byte.
//! 3. **Serializer rejection** — the shapes TOML cannot represent. Agreeing on
//!    accept while disagreeing on reject is a defect, and it is the half a
//!    round-trip test never reaches.
//! 4. **Panic hunting** — every case on both sides runs inside
//!    [`std::panic::catch_unwind`], so a panic is a recorded THIRD outcome next
//!    to Ok and Err rather than an abort. An incumbent that returns `Err` where
//!    we panic is a real behavioural difference in a library consumers call on
//!    untrusted input.

use std::fmt::Write as _;
use std::panic::{self, AssertUnwindSafe};

mod common;
use common::compare;

// ---------------------------------------------------------------------------
// Outcome: the three-valued result every probe produces.
// ---------------------------------------------------------------------------

/// What an implementation did with an input. `Panic` is a first-class outcome,
/// not an abort: the whole point of the panic family is to observe one.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome<T> {
    Ok(T),
    Err,
    Panic(String),
}

impl<T> Outcome<T> {
    fn tag(&self) -> &'static str {
        match self {
            Outcome::Ok(_) => "OK",
            Outcome::Err => "ERR",
            Outcome::Panic(_) => "PANIC",
        }
    }
}

/// Run `body` with panics captured and the default hook silenced, so a
/// deliberate panic probe does not print a backtrace for every case.
fn probe<T>(body: impl FnOnce() -> Result<T, String>) -> Outcome<T> {
    let previous = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let caught = panic::catch_unwind(AssertUnwindSafe(body));
    panic::set_hook(previous);
    match caught {
        Ok(Ok(value)) => Outcome::Ok(value),
        Ok(Err(_)) => Outcome::Err,
        Err(payload) => {
            let message = payload
                .downcast_ref::<&str>()
                .map(|s| (*s).to_string())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "<non-string panic payload>".to_string());
            Outcome::Panic(message)
        }
    }
}

fn parse_incumbent(text: &str) -> Outcome<incumbent_toml::Value> {
    probe(|| text.parse::<incumbent_toml::Value>().map_err(|e| e.to_string()))
}

fn parse_ours(text: &str) -> Outcome<trust_toml::Value> {
    probe(|| trust_toml::from_str::<trust_toml::Value>(text).map_err(|e| e.to_string()))
}

/// A readable rendering of a document for a failure message: control characters
/// escaped so the report is one line and copy-pasteable.
fn show(text: &str) -> String {
    let mut out = String::new();
    for character in text.chars() {
        match character {
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                let _ = write!(out, "\\u{{{:04x}}}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

// ---------------------------------------------------------------------------
// FAMILY 1 — the read path.
// ---------------------------------------------------------------------------

/// Every hazard document. Grouped by family so a failure names the family it
/// broke; no expectation is recorded, because the incumbent IS the expectation.
/// Writing one down would be writing a second TOML implementation in a table.
const READ_HAZARDS: &[(&str, &str)] = &[
    // -- integers: boundaries and radix ------------------------------------
    ("i64::MAX", "a = 9223372036854775807\n"),
    ("i64::MIN", "a = -9223372036854775808\n"),
    ("i64::MAX + 1", "a = 9223372036854775808\n"),
    ("i64::MIN - 1", "a = -9223372036854775809\n"),
    ("u64::MAX", "a = 18446744073709551615\n"),
    ("hex at i64::MAX", "a = 0x7fffffffffffffff\n"),
    ("hex one past i64::MAX", "a = 0x8000000000000000\n"),
    ("hex all ones", "a = 0xffffffffffffffff\n"),
    ("hex mixed case", "a = 0xDEADbeef\n"),
    ("octal", "a = 0o755\n"),
    ("octal max", "a = 0o777777777777777777777\n"),
    ("binary", "a = 0b11010110\n"),
    ("underscores", "a = 1_000_000\n"),
    ("underscore in hex", "a = 0xdead_beef\n"),
    ("underscore after radix prefix", "a = 0x_1\n"),
    ("trailing underscore", "a = 1_\n"),
    ("doubled underscore", "a = 1__0\n"),
    ("explicit plus", "a = +99\n"),
    ("negative zero integer", "a = -0\n"),
    ("positive zero integer", "a = +0\n"),
    ("plain zero", "a = 0\n"),
    ("leading zero", "a = 01\n"),
    ("signed hex", "a = -0x1\n"),
    ("radix prefix no digits", "a = 0x\n"),
    ("uppercase radix prefix", "a = 0X1\n"),
    // -- floats: the family the corpus cannot see --------------------------
    ("inf", "a = inf\n"),
    ("plus inf", "a = +inf\n"),
    ("minus inf", "a = -inf\n"),
    ("nan", "a = nan\n"),
    ("plus nan", "a = +nan\n"),
    ("minus nan", "a = -nan\n"),
    ("zero float", "a = 0.0\n"),
    ("negative zero float", "a = -0.0\n"),
    ("positive zero float", "a = +0.0\n"),
    ("pi", "a = 3.141592653589793\n"),
    ("exponent overflow", "a = 1e400\n"),
    ("exponent underflow", "a = 1e-400\n"),
    ("f64::MAX literal", "a = 1.7976931348623157e308\n"),
    ("f64::MIN_POSITIVE subnormal", "a = 5e-324\n"),
    ("capital E exponent", "a = 1E6\n"),
    ("signed exponent", "a = 5e+22\n"),
    ("physics constant", "a = 6.626e-34\n"),
    ("underscores in float", "a = 224_617.445_991_228\n"),
    ("integral-valued float", "a = 1.0\n"),
    ("float with zero exponent", "a = 1e0\n"),
    ("no leading digit", "a = .7\n"),
    ("no trailing digit", "a = 7.\n"),
    ("empty exponent", "a = 1e\n"),
    ("float with i64-overflowing mantissa", "a = 9223372036854775808.0\n"),
    ("many decimal places", "a = 0.1000000000000000055511151231257827\n"),
    // -- strings: escapes and the surrogate rule ---------------------------
    (
        "all simple escapes",
        r#"a = "\b\t\n\f\r\"\\"
"#,
    ),
    (
        "short unicode escape",
        r#"a = "\u00e9"
"#,
    ),
    (
        "long unicode escape",
        r#"a = "\U0001F600"
"#,
    ),
    (
        "lone high surrogate",
        r#"a = "\ud800"
"#,
    ),
    (
        "lone low surrogate",
        r#"a = "\udfff"
"#,
    ),
    (
        "surrogate pair spelled separately",
        r#"a = "\ud83d\ude00"
"#,
    ),
    (
        "escape past Unicode max",
        r#"a = "\U00110000"
"#,
    ),
    (
        "null escape",
        r#"a = "\u0000"
"#,
    ),
    (
        "hex escape (not TOML)",
        r#"a = "\x41"
"#,
    ),
    (
        "unknown escape",
        r#"a = "\q"
"#,
    ),
    (
        "escape at end of string",
        r#"a = "\"
"#,
    ),
    (
        "uppercase U short form",
        r#"a = "\U00e9"
"#,
    ),
    (
        "lowercase u long form",
        r#"a = "\u0001F600"
"#,
    ),
    ("literal string with backslashes", "a = 'C:\\Users\\n'\n"),
    ("literal string with quote", "a = 'he said \"hi\"'\n"),
    ("empty basic", "a = \"\"\n"),
    ("empty literal", "a = ''\n"),
    ("empty multiline basic", "a = \"\"\"\"\"\"\n"),
    ("empty multiline literal", "a = ''''''\n"),
    ("multiline leading newline trimmed", "a = \"\"\"\nfirst\n\"\"\"\n"),
    ("multiline line-ending backslash", "a = \"\"\"\\\n   continued\\\n   \"\"\"\n"),
    ("multiline with one trailing quote", "a = \"\"\"x\"\"\"\"\n"),
    ("multiline with two trailing quotes", "a = \"\"\"x\"\"\"\"\"\n"),
    ("multiline with three quotes inside", "a = \"\"\"x\"\"\"y\"\"\"\n"),
    ("multiline literal with one trailing quote", "a = '''x''''\n"),
    ("raw control char in basic", "a = \"\u{1}\"\n"),
    ("raw DEL in basic", "a = \"\u{7f}\"\n"),
    ("raw tab in basic", "a = \"\tx\"\n"),
    ("raw control char in literal", "a = '\u{1}'\n"),
    ("raw DEL in literal", "a = '\u{7f}'\n"),
    ("newline in basic", "a = \"x\ny\"\n"),
    ("newline in literal", "a = 'x\ny'\n"),
    ("CRLF in multiline basic", "a = \"\"\"\r\nx\r\ny\"\"\"\n"),
    ("bare CR in multiline basic", "a = \"\"\"x\ry\"\"\"\n"),
    ("bare CR outside a string", "a = 1\rb = 2\n"),
    ("astral plane literal", "a = \"\u{1F600}\"\n"),
    ("combining characters", "a = \"e\u{301}\"\n"),
    ("BOM inside a string", "a = \"\u{feff}\"\n"),
    // -- keys ---------------------------------------------------------------
    ("empty quoted key", "\"\" = 1\n"),
    ("empty literal key", "'' = 1\n"),
    ("dotted key", "a.b.c = 1\n"),
    ("quoted key containing a dot", "\"a.b\" = 1\n"),
    ("bare numeric key", "3 = \"x\"\n"),
    ("bare key that looks like a float", "3.14 = \"x\"\n"),
    ("bare key with dashes and underscores", "a-b_c = 1\n"),
    ("escaped key", "\"\\u00e9\" = 1\n"),
    ("non-ASCII bare key", "é = 1\n"),
    ("key with spaces around the dot", "a . b = 1\n"),
    ("whitespace-only quoted key", "\" \" = 1\n"),
    ("key that is a keyword", "true = 1\n"),
    // -- table identity -----------------------------------------------------
    ("duplicate top-level key", "a = 1\na = 2\n"),
    ("duplicate key differing by quoting", "a = 1\n\"a\" = 2\n"),
    ("duplicate header", "[t]\n[t]\n"),
    ("super-table defined after sub-table", "[a.b]\nx = 1\n[a]\ny = 2\n"),
    ("super-table defined twice implicitly", "[a.b]\n[a.c]\n"),
    ("header over an array of tables", "[[t]]\n[t]\n"),
    ("array-of-tables header over a table", "[t]\n[[t]]\n"),
    ("header reopening a dotted-key table", "a.b = 1\n[a]\n"),
    ("dotted key into a header table", "[a.b]\nx = 1\n[a]\nb.y = 2\n"),
    ("header extending a closed inline table", "a = { x = 1 }\n[a.b]\nc = 2\n"),
    ("header over a scalar", "a = 1\n[a]\n"),
    ("dotted key under a scalar", "a = 1\na.b = 2\n"),
    ("two array-of-table elements", "[[a]]\nx = 1\n[[a]]\nx = 2\n"),
    ("array of tables with sub-tables", "[[a]]\n[a.b]\nx = 1\n[[a]]\n[a.b]\nx = 2\n"),
    ("dotted key inside an array element", "[[a]]\nb.c = 1\n"),
    ("empty header path", "[]\n"),
    ("header with an empty segment", "[a..b]\n"),
    ("header with a quoted empty segment", "[a.\"\".b]\n"),
    // -- datetimes ----------------------------------------------------------
    ("offset datetime Z", "a = 1979-05-27T07:32:00Z\n"),
    ("offset datetime lowercase z", "a = 1979-05-27t07:32:00z\n"),
    ("offset datetime space separator", "a = 1979-05-27 07:32:00Z\n"),
    ("offset datetime negative offset", "a = 1979-05-27T00:32:00-07:00\n"),
    ("offset datetime plus offset", "a = 1979-05-27T00:32:00+07:00\n"),
    ("offset datetime with fraction", "a = 1979-05-27T00:32:00.999999-07:00\n"),
    ("local datetime", "a = 1979-05-27T07:32:00\n"),
    ("local date", "a = 1979-05-27\n"),
    ("local time", "a = 07:32:00\n"),
    ("local time with fraction", "a = 00:32:00.999999\n"),
    ("leap second", "a = 1979-05-27T23:59:60Z\n"),
    ("impossible day", "a = 2026-02-30\n"),
    ("month zero", "a = 2026-00-01\n"),
    ("month thirteen", "a = 2026-13-01\n"),
    ("hour 24", "a = 24:00:00\n"),
    ("minute 60", "a = 00:60:00\n"),
    ("leap day in a leap year", "a = 2024-02-29\n"),
    ("leap day in a non-leap year", "a = 2023-02-29\n"),
    ("nanosecond fraction", "a = 00:32:00.123456789\n"),
    ("over-precise fraction", "a = 00:32:00.123456789012\n"),
    ("offset with seconds", "a = 1979-05-27T00:32:00-07:00:30\n"),
    ("two-digit year", "a = 79-05-27\n"),
    ("negative zero offset", "a = 1979-05-27T00:32:00-00:00\n"),
    // -- arrays and inline tables ------------------------------------------
    ("trailing comma in array", "a = [1, 2, 3,]\n"),
    ("double trailing comma in array", "a = [1, 2,,]\n"),
    ("heterogeneous array", "a = [1, \"x\", true]\n"),
    ("array across newlines with comments", "a = [\n 1,\n # note\n 2,\n]\n"),
    ("empty array", "a = []\n"),
    ("nested arrays", "a = [[1, 2], [3]]\n"),
    ("array of inline tables", "a = [{x = 1}, {x = 2}]\n"),
    ("inline table", "a = {x = 1, y = 2}\n"),
    ("empty inline table", "a = {}\n"),
    ("trailing comma in inline table", "a = {x = 1,}\n"),
    ("newline inside inline table", "a = {\n x = 1\n}\n"),
    ("nested inline tables", "a = {b = {c = 1}}\n"),
    ("dotted key inside an inline table", "a = {b.c = 1}\n"),
    ("duplicate key inside an inline table", "a = {b = 1, b = 2}\n"),
    ("array containing only a comment", "a = [\n # nothing\n]\n"),
    ("unterminated array", "a = [1, 2\n"),
    ("unterminated inline table", "a = {x = 1\n"),
    // -- document structure -------------------------------------------------
    ("byte order mark", "\u{feff}a = 1\n"),
    ("empty document", ""),
    ("only a comment", "# nothing here\n"),
    ("no trailing newline", "a = 1"),
    ("CRLF line endings", "a = 1\r\nb = 2\r\n"),
    ("control char in a comment", "# \u{1}\n"),
    ("DEL in a comment", "# \u{7f}\n"),
    ("value missing", "a =\n"),
    ("key missing", "= 1\n"),
    ("two values on one line", "a = 1 b = 2\n"),
    ("trailing junk after a value", "a = 1 junk\n"),
    ("comment after a value", "a = 1 # note\n"),
    ("header with trailing junk", "[a] junk\n"),
    ("bare true and false", "a = true\nb = false\n"),
    ("capitalised boolean", "a = True\n"),
];

/// `0b` followed by sixty-four `1`s — `u64::MAX` in binary, one past `i64::MAX`.
/// Built rather than typed so a miscount is impossible.
fn binary_64_ones() -> String {
    format!("a = 0b{}\n", "1".repeat(64))
}

/// The read-path differential. Every hazard, both implementations, three-valued
/// outcome, tree comparison on mutual acceptance.
#[test]
fn the_read_path_agrees_with_the_incumbent_on_every_hand_enumerated_hazard() {
    let owned = binary_64_ones();
    let mut cases: Vec<(&str, &str)> = READ_HAZARDS.to_vec();
    // Sixty-four binary `1`s is `u64::MAX`: one past `i64::MAX`, and the case
    // most likely to be a silent wrapping difference rather than a rejection.
    // Built rather than typed, so a miscount cannot make it a weaker probe.
    cases.push(("binary 64 ones", owned.as_str()));

    let mut failures: Vec<String> = Vec::new();
    for (name, document) in &cases {
        let theirs = parse_incumbent(document);
        let ours = parse_ours(document);
        match (&theirs, &ours) {
            (Outcome::Ok(left), Outcome::Ok(right)) => {
                let mut differences = Vec::new();
                compare(left, right, "", &mut differences);
                if !differences.is_empty() {
                    failures.push(format!(
                        "{name}: both accepted `{}` but the trees differ:\n      {}",
                        show(document),
                        differences.join("\n      ")
                    ));
                }
            }
            (Outcome::Err, Outcome::Err) => {}
            _ => failures.push(format!(
                "{name}: `{}` — incumbent {}{}, trust-toml {}{}",
                show(document),
                theirs.tag(),
                match &theirs {
                    Outcome::Ok(v) => format!(" ({v:?})"),
                    Outcome::Panic(m) => format!(" [{m}]"),
                    Outcome::Err => String::new(),
                },
                ours.tag(),
                match &ours {
                    Outcome::Ok(v) => format!(" ({v:?})"),
                    Outcome::Panic(m) => format!(" [{m}]"),
                    Outcome::Err => String::new(),
                },
            )),
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} read hazards disagree with the incumbent:\n  - {}",
        failures.len(),
        cases.len(),
        failures.join("\n  - ")
    );
}

// ---------------------------------------------------------------------------
// FAMILY 2 — the write path, byte for byte.
// ---------------------------------------------------------------------------

/// Build the same document on both sides from a TOML source both accept, then
/// emit with both and compare bytes. Going through a parse rather than
/// hand-building two trees is deliberate: it keeps the two inputs provably the
/// same value (family 1 already asserts the trees are equal) instead of relying
/// on two hand transcriptions staying in step.
fn emit_both(document: &str) -> Option<(Outcome<String>, Outcome<String>)> {
    let theirs_tree = match parse_incumbent(document) {
        Outcome::Ok(tree) => tree,
        _ => return None,
    };
    let ours_tree = match parse_ours(document) {
        Outcome::Ok(tree) => tree,
        _ => return None,
    };
    let theirs = probe(|| incumbent_toml::to_string(&theirs_tree).map_err(|e| e.to_string()));
    let ours = probe(|| trust_toml::to_string(&ours_tree).map_err(|e| e.to_string()));
    Some((theirs, ours))
}

/// Values whose *spelling* on the way out is the hazard. Each is a complete
/// document that both implementations accept (family 1 proves that separately).
const WRITE_HAZARDS: &[(&str, &str)] = &[
    ("integral float", "a = 1.0\n"),
    ("negative zero float", "a = -0.0\n"),
    ("positive zero float", "a = 0.0\n"),
    ("nan", "a = nan\n"),
    ("minus nan", "a = -nan\n"),
    ("inf", "a = inf\n"),
    ("minus inf", "a = -inf\n"),
    ("large exponent", "a = 1e300\n"),
    ("small exponent", "a = 1e-300\n"),
    ("f64::MAX", "a = 1.7976931348623157e308\n"),
    ("subnormal", "a = 5e-324\n"),
    ("pi", "a = 3.141592653589793\n"),
    ("one tenth", "a = 0.1\n"),
    ("float that needs seventeen digits", "a = 0.30000000000000004\n"),
    ("i64::MAX", "a = 9223372036854775807\n"),
    ("i64::MIN", "a = -9223372036854775808\n"),
    ("negative zero integer", "a = -0\n"),
    ("hex input", "a = 0xdeadbeef\n"),
    ("octal input", "a = 0o755\n"),
    ("binary input", "a = 0b1011\n"),
    ("underscored input", "a = 1_000_000\n"),
    ("string with every simple escape", "a = \"\\b\\t\\n\\f\\r\\\"\\\\\"\n"),
    ("string with a tab", "a = \"x\\ty\"\n"),
    ("string with a newline", "a = \"x\\ny\"\n"),
    ("string with a CR", "a = \"x\\ry\"\n"),
    ("string with a NUL", "a = \"\\u0000\"\n"),
    ("string with a DEL", "a = \"\\u007f\"\n"),
    ("string with an apostrophe", "a = \"it's\"\n"),
    ("string with a quote", "a = 'say \"hi\"'\n"),
    ("string with both quote kinds", "a = \"a\\\"b'c\"\n"),
    ("string with three apostrophes", "a = \"a'''b\"\n"),
    ("string with three quotes", "a = 'a\"\"\"b'\n"),
    ("string ending in a quote", "a = 'x\"'\n"),
    ("string ending in an apostrophe", "a = \"x'\"\n"),
    ("string of only a backslash", "a = \"\\\\\"\n"),
    ("astral plane string", "a = \"\u{1F600}\"\n"),
    ("string with a BOM", "a = \"\u{feff}\"\n"),
    ("multiline string", "a = \"\"\"\nline one\nline two\n\"\"\"\n"),
    ("multiline string with a quote", "a = \"\"\"\nsay \"hi\"\n\"\"\"\n"),
    ("empty string", "a = \"\"\n"),
    ("key needing quotes", "\"a b\" = 1\n"),
    ("key with a dot", "\"a.b\" = 1\n"),
    ("empty key", "\"\" = 1\n"),
    ("key with a quote", "\"a\\\"b\" = 1\n"),
    ("non-ASCII key", "\"é\" = 1\n"),
    ("numeric-looking key", "3 = 1\n"),
    ("empty table", "[a]\n"),
    ("empty nested table", "[a.b]\n"),
    ("table with values and sub-tables", "[a]\nx = 1\n[a.b]\ny = 2\n"),
    ("array of tables", "[[a]]\nx = 1\n[[a]]\nx = 2\n"),
    ("empty array of tables value", "a = []\n"),
    ("array of empty tables", "a = [{}, {}]\n"),
    ("nested array", "a = [[1, 2], [3]]\n"),
    ("heterogeneous array", "a = [1, \"x\", true]\n"),
    ("array of strings", "a = [\"x\", \"y\"]\n"),
    ("offset datetime", "a = 1979-05-27T07:32:00Z\n"),
    ("offset datetime with offset", "a = 1979-05-27T00:32:00-07:00\n"),
    ("local datetime", "a = 1979-05-27T07:32:00\n"),
    ("local date", "a = 1979-05-27\n"),
    ("local time", "a = 07:32:00\n"),
    ("local time with fraction", "a = 00:32:00.999999\n"),
    ("booleans", "a = true\nb = false\n"),
    ("deeply nested tables", "[a.b.c.d.e]\nx = 1\n"),
    ("sub-table of an array element", "[[a]]\n[a.b]\nx = 1\n"),
];

#[test]
fn emitted_bytes_match_the_incumbent_on_every_hand_enumerated_write_hazard() {
    let mut failures: Vec<String> = Vec::new();
    let mut compared = 0usize;
    for (name, document) in WRITE_HAZARDS {
        let Some((theirs, ours)) = emit_both(document) else {
            failures.push(format!("{name}: `{}` was not readable by both", show(document)));
            continue;
        };
        compared += 1;
        match (&theirs, &ours) {
            (Outcome::Ok(left), Outcome::Ok(right)) if left == right => {}
            (Outcome::Ok(left), Outcome::Ok(right)) => failures.push(format!(
                "{name}: `{}`\n      incumbent  `{}`\n      trust-toml `{}`",
                show(document),
                show(left),
                show(right)
            )),
            _ => failures.push(format!(
                "{name}: `{}` — incumbent {}{}, trust-toml {}{}",
                show(document),
                theirs.tag(),
                if let Outcome::Panic(m) = &theirs { format!(" [{m}]") } else { String::new() },
                ours.tag(),
                if let Outcome::Panic(m) = &ours { format!(" [{m}]") } else { String::new() },
            )),
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} write hazards disagree with the incumbent byte-for-byte:\n  - {}",
        failures.len(),
        compared,
        failures.join("\n  - ")
    );
}

/// The write path's own round trip, across the implementation boundary: our
/// text, re-read by the INCUMBENT, must equal the incumbent's own tree.
///
/// Separate from the byte test because they fail for different reasons and one
/// is a much more serious failure than the other. A byte difference is a
/// cosmetic disagreement about spelling; a value difference is data loss.
#[test]
fn emitted_text_reread_by_the_incumbent_preserves_every_hazard_value() {
    let mut failures: Vec<String> = Vec::new();
    for (name, document) in WRITE_HAZARDS {
        let Outcome::Ok(reference) = parse_incumbent(document) else { continue };
        let Outcome::Ok(ours_tree) = parse_ours(document) else { continue };
        let Outcome::Ok(text) =
            probe(|| trust_toml::to_string(&ours_tree).map_err(|e| e.to_string()))
        else {
            failures.push(format!("{name}: trust-toml could not emit `{}`", show(document)));
            continue;
        };
        match parse_incumbent(&text) {
            Outcome::Ok(reread) => {
                let mut differences = Vec::new();
                common::compare_incumbent(&reference, &reread, "", &mut differences);
                if !differences.is_empty() {
                    failures.push(format!(
                        "{name}: `{}` emitted as `{}` re-reads differently:\n      {}",
                        show(document),
                        show(&text),
                        differences.join("\n      ")
                    ));
                }
            }
            other => failures.push(format!(
                "{name}: `{}` emitted as `{}` which the incumbent {}",
                show(document),
                show(&text),
                other.tag()
            )),
        }
    }
    assert!(
        failures.is_empty(),
        "{} write hazards lose or change a value across the boundary:\n  - {}",
        failures.len(),
        failures.join("\n  - ")
    );
}

// ---------------------------------------------------------------------------
// The deliberate divergences.
//
// Two, both named, both with the incumbent source line that produced them.
// This is an allowlist, and an allowlist that can grow quietly is the failure
// mode it is supposed to prevent — so each is a NAMED test asserting the exact
// pair of outcomes, not an entry skipped inside a loop. A third divergence
// cannot be added without writing a third test and saying why.
// ---------------------------------------------------------------------------

/// `-1e400` is refused here and accepted by the incumbent as `-inf`.
///
/// `toml_edit-0.22.27`, `src/parser/numbers.rs:203`, guards float overflow with
/// `.verify(|f: &f64| *f != f64::INFINITY)` — positive infinity only. So
/// `a = 1e400` is refused there and `a = -1e400` sails through. This crate
/// applies the rule to both signs (`src/parser.rs`, `parse_number`), because a
/// finite literal silently becoming `-inf` is the same defect as it becoming
/// `inf`, and copying a one-sided guard is copying a typo.
#[test]
fn the_only_read_path_divergence_is_negative_float_overflow_and_it_is_deliberate() {
    let document = "a = -1e400\n";
    assert!(
        matches!(parse_incumbent(document), Outcome::Ok(_)),
        "the incumbent still accepts negative overflow — if this fails it was fixed upstream \
         and this divergence should be retired"
    );
    assert!(matches!(parse_ours(document), Outcome::Err), "and we still refuse it");

    // The positive twin is NOT a divergence, and did not used to hold: before
    // the adversarial run we accepted `a = 1e400` as `inf` where the incumbent
    // returned `Err`. Pinned here so a revert is visible.
    assert!(matches!(parse_incumbent("a = 1e400\n"), Outcome::Err));
    assert!(matches!(parse_ours("a = 1e400\n"), Outcome::Err));
}

/// An `i128` whose value fits `i64` is written here and refused by the
/// incumbent, which rejects the whole type.
///
/// Kept, rather than matched, because the emitted value is exact and reads back
/// exactly — asserted below, not asserted about. Out-of-range `i128` is still
/// refused by both, which is the half that matters.
#[test]
fn the_only_write_path_divergence_is_in_range_i128_and_it_round_trips() {
    #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq)]
    struct Wide {
        v: i128,
    }

    let value = Wide { v: 5 };
    assert!(
        incumbent_toml::to_string(&value).is_err(),
        "the incumbent refuses i128 outright — if this fails it gained support and the \
         divergence should be retired"
    );
    let text = trust_toml::to_string(&value).expect("an in-range i128 has an exact TOML spelling");
    assert_eq!(text, "v = 5\n");
    assert_eq!(trust_toml::from_str::<Wide>(&text).unwrap(), value, "and it reads back exactly");

    // The dangerous half is not divergent: out of range, both refuse.
    assert!(trust_toml::to_string(&Wide { v: i128::MAX }).is_err());
    assert!(incumbent_toml::to_string(&Wide { v: i128::MAX }).is_err());
}

// ---------------------------------------------------------------------------
// FAMILY 3 — serializer rejection agreement.
//
// A round-trip test can only visit values that round-trip. Everything TOML
// cannot represent is invisible to it, and "agreeing on accept while
// disagreeing on reject" is exactly the defect that hides there. Each case
// below is a distinct Rust type, so this is a list of closures rather than a
// table of data.
// ---------------------------------------------------------------------------

/// Compare `to_string` outcomes on both sides for one value.
///
/// Only the OUTCOME is compared — Ok vs Err vs panic, and the emitted bytes
/// when both are Ok. Message text is deliberately not compared: pinning this
/// crate to `toml 0.8`'s prose would make its next release a build break here,
/// and every refusal's quality is asserted separately (each must name the fix).
fn compare_serialize<T: serde::Serialize>(
    name: &'static str,
    value: &T,
    failures: &mut Vec<String>,
) {
    let theirs = probe(|| incumbent_toml::to_string(value).map_err(|e| e.to_string()));
    let ours = probe(|| trust_toml::to_string(value).map_err(|e| e.to_string()));
    match (&theirs, &ours) {
        (Outcome::Ok(left), Outcome::Ok(right)) if left == right => {}
        (Outcome::Ok(left), Outcome::Ok(right)) => failures.push(format!(
            "{name}: both wrote, but differently — incumbent `{}`, trust-toml `{}`",
            show(left),
            show(right)
        )),
        (Outcome::Err, Outcome::Err) => {
            // Both refuse. Assert this crate's own quality bar on the refusal:
            // principle 10 — a refusal must carry the fix.
            if let Err(error) = trust_toml::to_string(value) {
                if !error.message().contains("Options:") {
                    failures.push(format!("{name}: refused without naming a fix: {error}"));
                }
            }
        }
        _ => failures.push(format!(
            "{name}: incumbent {}{}, trust-toml {}{}",
            theirs.tag(),
            match &theirs {
                Outcome::Ok(v) => format!(" (`{}`)", show(v)),
                Outcome::Panic(m) => format!(" [{m}]"),
                Outcome::Err => String::new(),
            },
            ours.tag(),
            match &ours {
                Outcome::Ok(v) => format!(" (`{}`)", show(v)),
                Outcome::Panic(m) => format!(" [{m}]"),
                Outcome::Err => String::new(),
            },
        )),
    }
}

#[test]
fn the_write_path_agrees_with_the_incumbent_on_what_it_refuses() {
    use std::collections::BTreeMap;

    use serde::Serialize;

    #[derive(Serialize)]
    struct Inner {
        x: i32,
    }
    #[derive(Serialize)]
    struct WithNone {
        a: i32,
        b: Option<i32>,
    }
    #[derive(Serialize)]
    struct WithUnit {
        a: (),
    }
    #[derive(Serialize)]
    struct UnitStruct;
    #[derive(Serialize)]
    struct WithUnitStruct {
        a: UnitStruct,
    }
    #[derive(Serialize)]
    struct NewtypeStruct(i32);
    #[derive(Serialize)]
    struct WithBytes<'a> {
        #[serde(with = "bytes_field")]
        a: &'a [u8],
    }
    mod bytes_field {
        pub fn serialize<S: serde::Serializer>(v: &&[u8], s: S) -> Result<S::Ok, S::Error> {
            s.serialize_bytes(v)
        }
    }
    #[derive(Serialize)]
    struct Floats {
        nan: f64,
        inf: f64,
        ninf: f64,
    }
    #[derive(Serialize)]
    struct BigU {
        u: u64,
    }
    #[derive(Serialize)]
    struct NestedOption {
        a: Option<Option<i32>>,
    }
    #[derive(Serialize)]
    struct ArrayWithNone {
        a: Vec<Option<i32>>,
    }
    #[derive(Serialize)]
    struct TableThenScalar {
        t: Inner,
        s: i32,
    }
    #[derive(Serialize)]
    struct ArrayOfTablesThenScalar {
        t: Vec<Inner>,
        s: i32,
    }
    #[derive(Serialize)]
    enum Variants {
        Unit,
        New(i32),
        Tup(i32, i32),
        Struct { x: i32 },
    }
    #[derive(Serialize)]
    struct Holder {
        e: Variants,
    }
    #[derive(Serialize)]
    struct EmptyKey {
        #[serde(rename = "")]
        v: i32,
    }
    #[derive(Serialize)]
    struct DuplicateKeys {
        #[serde(rename = "a")]
        one: i32,
        #[serde(rename = "a")]
        two: i32,
    }

    let mut failures = Vec::new();

    // -- a document is a table; nothing else is ----------------------------
    compare_serialize("top-level integer", &1_i64, &mut failures);
    compare_serialize("top-level string", &"x", &mut failures);
    compare_serialize("top-level bool", &true, &mut failures);
    compare_serialize("top-level float", &1.5_f64, &mut failures);
    compare_serialize("top-level array", &vec![1, 2, 3], &mut failures);
    compare_serialize("top-level None", &Option::<i32>::None, &mut failures);
    compare_serialize("top-level unit", &(), &mut failures);
    compare_serialize("top-level Some", &Some(1), &mut failures);
    compare_serialize("top-level newtype struct", &NewtypeStruct(1), &mut failures);
    compare_serialize("top-level unit struct", &UnitStruct, &mut failures);
    compare_serialize("top-level unit variant", &Variants::Unit, &mut failures);
    compare_serialize("top-level struct variant", &Variants::Struct { x: 1 }, &mut failures);
    compare_serialize("top-level empty map", &BTreeMap::<String, i32>::new(), &mut failures);

    // -- the null-shaped family: TOML has no null --------------------------
    compare_serialize("None field is dropped", &WithNone { a: 1, b: None }, &mut failures);
    compare_serialize("Some field is written", &WithNone { a: 1, b: Some(2) }, &mut failures);
    compare_serialize("unit field", &WithUnit { a: () }, &mut failures);
    compare_serialize("unit-struct field", &WithUnitStruct { a: UnitStruct }, &mut failures);
    compare_serialize("Some(None)", &NestedOption { a: Some(None) }, &mut failures);
    compare_serialize("Some(Some)", &NestedOption { a: Some(Some(1)) }, &mut failures);
    compare_serialize("outer None", &NestedOption { a: None }, &mut failures);
    compare_serialize(
        "None inside an array",
        &ArrayWithNone { a: vec![Some(1), None] },
        &mut failures,
    );

    // -- numeric range and shape -------------------------------------------
    compare_serialize("u64 above i64::MAX", &BigU { u: u64::MAX }, &mut failures);
    compare_serialize("u64 at i64::MAX", &BigU { u: i64::MAX as u64 }, &mut failures);
    compare_serialize(
        "nan and both infinities",
        &Floats { nan: f64::NAN, inf: f64::INFINITY, ninf: f64::NEG_INFINITY },
        &mut failures,
    );

    // -- bytes ---------------------------------------------------------------
    compare_serialize("bytes field", &WithBytes { a: b"hi" }, &mut failures);
    compare_serialize("empty bytes field", &WithBytes { a: b"" }, &mut failures);

    // -- map keys ------------------------------------------------------------
    compare_serialize("integer map keys", &BTreeMap::from([(1_i32, 2_i32)]), &mut failures);
    compare_serialize("bool map keys", &BTreeMap::from([(true, 2_i32)]), &mut failures);
    compare_serialize("char map keys", &BTreeMap::from([('a', 2_i32)]), &mut failures);
    compare_serialize("tuple map keys", &BTreeMap::from([((1_i32, 2_i32), 3_i32)]), &mut failures);
    compare_serialize(
        "string map key needing quotes",
        &BTreeMap::from([("a b".to_string(), 1_i32)]),
        &mut failures,
    );
    compare_serialize(
        "string map key with a newline",
        &BTreeMap::from([("a\nb".to_string(), 1_i32)]),
        &mut failures,
    );
    compare_serialize(
        "string map key with a quote",
        &BTreeMap::from([("a\"b".to_string(), 1_i32)]),
        &mut failures,
    );
    compare_serialize("empty key", &EmptyKey { v: 1 }, &mut failures);
    compare_serialize(
        "two fields renamed to one key",
        &DuplicateKeys { one: 1, two: 2 },
        &mut failures,
    );

    // -- ordering and enum shapes -------------------------------------------
    compare_serialize(
        "a table field declared before a scalar one",
        &TableThenScalar { t: Inner { x: 1 }, s: 2 },
        &mut failures,
    );
    compare_serialize(
        "an array-of-tables field declared before a scalar one",
        &ArrayOfTablesThenScalar { t: vec![Inner { x: 1 }], s: 2 },
        &mut failures,
    );
    compare_serialize("unit variant", &Holder { e: Variants::Unit }, &mut failures);
    compare_serialize("newtype variant", &Holder { e: Variants::New(1) }, &mut failures);
    compare_serialize("tuple variant", &Holder { e: Variants::Tup(1, 2) }, &mut failures);
    compare_serialize("struct variant", &Holder { e: Variants::Struct { x: 1 } }, &mut failures);

    assert!(
        failures.is_empty(),
        "{} serializer cases disagree with the incumbent:\n  - {}",
        failures.len(),
        failures.join("\n  - ")
    );
}

// ---------------------------------------------------------------------------
// FAMILY 4 — recursion.
//
// This family found the worst defect of the run, and it is the one a
// `catch_unwind`-based harness reports as a PASS: a stack overflow is an
// ABORT, not a panic, so a test that merely wraps the call sees nothing and
// the process dies. It is caught here by asserting the DECLARED limit instead
// — a construct one level past the limit must return `Err`, which can only be
// observed if the parser never descends far enough to overflow.
// ---------------------------------------------------------------------------

fn nested_array(depth: usize) -> String {
    format!("a = {}1{}\n", "[".repeat(depth), "]".repeat(depth))
}

fn nested_inline_table(depth: usize) -> String {
    let mut text = String::from("a = ");
    for _ in 0..depth {
        text.push_str("{b = ");
    }
    text.push('1');
    for _ in 0..depth {
        text.push('}');
    }
    text.push('\n');
    text
}

fn deep_header(depth: usize) -> String {
    let path: Vec<String> = (0..depth).map(|index| format!("k{index}")).collect();
    format!("[{}]\nx = 1\n", path.join("."))
}

/// The limit is where the incumbent's is, at every construct that has one.
///
/// Reaching this test at all is the evidence: before the limit existed, a
/// depth-5000 array aborted the process here rather than failing an assertion.
#[test]
fn nesting_is_bounded_at_exactly_the_incumbents_limit() {
    let shapes: [(&str, fn(usize) -> String); 3] = [
        ("nested arrays", nested_array),
        ("nested inline tables", nested_inline_table),
        ("dotted header path", deep_header),
    ];
    let mut failures = Vec::new();
    for (name, build) in shapes {
        for depth in [1, 40, 78, 79, 80, 81, 200, 5_000, 100_000] {
            let document = build(depth);
            let theirs = parse_incumbent(&document);
            let ours = parse_ours(&document);
            let agree = matches!(
                (&theirs, &ours),
                (Outcome::Ok(_), Outcome::Ok(_)) | (Outcome::Err, Outcome::Err)
            );
            if !agree {
                failures.push(format!(
                    "{name} at depth {depth}: incumbent {}, trust-toml {}",
                    theirs.tag(),
                    ours.tag()
                ));
            }
        }
        // And the boundary itself, stated rather than inferred from the sweep:
        // 79 in, 80 out. `toml_edit`'s `RecursionCheck::enter` increments then
        // tests `LIMIT <= current`, so the limit is the first REFUSED depth.
        if !matches!(parse_ours(&build(79)), Outcome::Ok(_)) {
            failures.push(format!("{name}: depth 79 must be accepted"));
        }
        if !matches!(parse_ours(&build(80)), Outcome::Err) {
            failures.push(format!("{name}: depth 80 must be refused"));
        }
    }
    assert!(
        failures.is_empty(),
        "recursion bounds disagree with the incumbent:\n  - {}",
        failures.join("\n  - ")
    );
}

/// Depth is NESTING, not a running total — the counter must come back down.
///
/// A high-water-mark implementation passes the test above and fails this one:
/// a document with a hundred sibling arrays would be refused even though
/// nothing in it is nested more than one level deep.
#[test]
fn depth_is_nesting_and_not_a_running_total() {
    let one_deep_many_times: String =
        (0..500).map(|index| format!("k{index} = [[1], [2]]\n")).collect();
    assert!(matches!(parse_ours(&one_deep_many_times), Outcome::Ok(_)));
    assert!(matches!(parse_incumbent(&one_deep_many_times), Outcome::Ok(_)));

    // Same for a sequence of deep-but-legal headers.
    let many_headers: String =
        (0..200).map(|index| deep_header(70).replace("k0", &format!("t{index}"))).collect();
    assert!(matches!(parse_ours(&many_headers), Outcome::Ok(_)));
    assert!(matches!(parse_incumbent(&many_headers), Outcome::Ok(_)));
}
