// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Rendering a [`Node`] tree as TOML text — the second half of the write path.
//!
//! [`crate::ser`] turns any `Serialize` value into a `Node`; this module turns a
//! `Node` into bytes. The split is not decoration. Serialization decides *what*
//! the document contains and can fail (a `None` in an array has no TOML
//! spelling); emission decides *how* it is spelled and, once a `Node` exists,
//! cannot fail at all — every `Node` has a valid rendering. Keeping them apart
//! means the failure modes of the write path are enumerated in exactly one file.
//!
//! # The two rules that make emitted TOML *correct* rather than merely parseable
//!
//! A TOML writer's characteristic bug is a document that is valid TOML and means
//! something else. Two rules prevent it, and both are structural here rather
//! than conventional:
//!
//! 1. **Values before sub-tables, always.** After a `[a]` header every following
//!    `key = value` line belongs to `a`. So a table's own scalar entries must
//!    all be written before its first sub-table header, or they silently move
//!    into the sub-table. [`write_body`] therefore makes two passes over the
//!    entries — values, then children — and never one. This is the single most
//!    dangerous thing a naive `for (k, v) in table` loop gets wrong, and it
//!    produces a document that parses.
//! 2. **A key is quoted unless it is provably bare.** `a.b` written unquoted is
//!    a *dotted key* — it means `{a: {b: …}}`, not the key `"a.b"`.
//!    [`render_key`] quotes anything that is not entirely `[A-Za-z0-9_-]`, using
//!    the same predicate the parser uses to *read* bare keys
//!    ([`crate::parser::is_bare_key_byte`]), so the two cannot drift apart.
//!
//! # Header suppression, and why it is round-trip-safe
//!
//! A table whose entries are *all* sub-tables or arrays-of-tables gets no header
//! of its own: `{a: {b: {c: {x: 1}}}}` emits `[a.b.c]` alone, which is what the
//! incumbent emits (measured). Re-reading that document recreates `a` and `a.b`
//! implicitly, so the tree round-trips exactly. The one table that must always
//! be declared is an **empty** one — `[sub]` with nothing under it — because
//! there is no other evidence of its existence.
//!
//! # What is asserted against the incumbent, and what is not
//!
//! The acceptance gate for the write path is a **round-trip differential**
//! (`tests/serialize_differential.rs`): our text, re-read by `toml 0.8`, must
//! yield the tree the incumbent read from the original document. That is the
//! contract — value preservation — and it is what a consumer depends on.
//!
//! Byte-identity with the incumbent's emitter is *not* the contract, but it is
//! measured, because a gratuitous spelling change lands in reviewed files. The
//! measurements over the 1,377 readable corpus documents:
//!
//! | emitter | corpus byte-identity |
//! |---|---|
//! | always a one-line basic string (first draft) | 96.66% |
//! | [`StringForm`], the rule below | **100.00%** |
//!
//! Three tests keep the distinction honest: byte-identity is *required* on the
//! seven documents this repository's own tooling writes, *floored* corpus-wide
//! so a regression is visible, and the string rule itself is re-derived against
//! the incumbent over 21,563 generated strings on every run. The only class
//! where the spelling is still allowed to differ is named by a predicate, not a
//! list — see `is_mixed_quote` in `tests/serialize_differential.rs` — and no
//! corpus document is in it.
//!
//! Known and deliberate: **table iteration order** is the order the [`Node`]
//! carries, which is the order `serde` presented the fields in — matching the
//! incumbent. See [`crate::ser`] for why the intermediate is an ordered `Vec`
//! and not a [`crate::Map`].

use std::fmt::Write as _;

use crate::parser::is_bare_key_byte;

/// The ordered intermediate the write path builds and then renders.
///
/// It is **not** [`crate::Value`], and the difference is the whole reason it
/// exists: `Value`'s table is a [`crate::Map`], which is `BTreeMap`-backed and
/// therefore key-sorted. Serializing a struct through `Value` would silently
/// re-order its fields, so `to_string` on a struct would emit fields in
/// alphabetical order where the incumbent emits them in declaration order. That
/// is a visible, gratuitous difference in every file this workspace writes. A
/// `Vec<(String, Node)>` keeps `serde`'s presentation order.
///
/// A `Value` fed to `to_string` still comes out key-sorted, because its own map
/// is sorted — which is also what the incumbent does with its own `Value`. Both
/// inputs behave like the incumbent; that is the point.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Node {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    /// A datetime, already rendered to its canonical TOML text.
    ///
    /// Held as text rather than as a [`crate::Datetime`] because that is the
    /// form it arrives in: `serde` has no datetime type, so a datetime reaches a
    /// serializer as the reserved one-entry map documented in
    /// [`crate::datetime`], carrying its canonical spelling as a string. Parsing
    /// that string back into a `Datetime` only to print it again would be a
    /// round trip through a lossy-looking step for no gain.
    Datetime(String),
    Array(Vec<Node>),
    Table(Vec<(String, Node)>),
}

impl Node {
    pub(crate) fn is_table(&self) -> bool {
        matches!(self, Self::Table(_))
    }

    /// Whether this node is written as `[[key]]` blocks rather than as an
    /// inline array.
    ///
    /// Non-empty **and** every element a table. Both halves matter. An empty
    /// `Vec<SomeStruct>` has no tables to write blocks for, so it must be
    /// emitted as `key = []` or it vanishes from the document entirely — the
    /// incumbent does the same (measured: `empty_tabs = []`). A mixed array
    /// cannot use the block form at all, because `[[key]]` can only express
    /// tables.
    pub(crate) fn is_array_of_tables(&self) -> bool {
        matches!(self, Self::Array(items) if !items.is_empty() && items.iter().all(Self::is_table))
    }

    /// Whether this entry occupies a `key = value` line, as opposed to a
    /// `[header]` / `[[header]]` block. The two are written in separate passes;
    /// see the module docs, rule 1.
    fn is_inline_entry(&self) -> bool {
        !self.is_table() && !self.is_array_of_tables()
    }
}

/// Array formatting. The only thing `to_string_pretty` changes.
///
/// Measured against `toml 0.8.23`: `to_string_pretty` differs from `to_string`
/// **only** in that an array with two or more elements is broken one element per
/// line with a four-space indent and a trailing comma. Arrays of length 0 and 1
/// stay inline in both, and strings, tables and headers are identical in both.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Style {
    /// `key = [1, 2, 3]`.
    Compact,
    /// `key = [` / `    1,` / … / `]`, for arrays of length >= 2.
    Pretty,
}

/// Render a root table as a TOML document.
///
/// Infallible: every [`Node`] has a valid rendering. The write path's failures
/// all happen earlier, in [`crate::ser`], where the `Serialize` value is turned
/// into a `Node` at all.
pub(crate) fn document(root: &[(String, Node)], style: Style) -> String {
    let mut out = String::new();
    let mut path: Vec<&str> = Vec::new();
    write_body(&mut out, &mut path, root, style);
    out
}

/// A table's contents: inline entries first, then child blocks. See the module
/// docs, rule 1 — the two passes are the correctness property, not a style.
fn write_body<'a>(
    out: &mut String,
    path: &mut Vec<&'a str>,
    entries: &'a [(String, Node)],
    style: Style,
) {
    for (key, node) in entries.iter().filter(|(_, node)| node.is_inline_entry()) {
        let _ = writeln!(out, "{} = {}", render_key(key), render_inline(node, style, 0));
    }
    for (key, node) in entries {
        match node {
            Node::Table(sub) => {
                path.push(key);
                write_table(out, path, sub, style);
                path.pop();
            }
            Node::Array(items) if node.is_array_of_tables() => {
                for item in items {
                    let Node::Table(sub) = item else {
                        unreachable!("is_array_of_tables checked every element is a table")
                    };
                    path.push(key);
                    write_header(out, path, true);
                    write_body(out, path, sub, style);
                    path.pop();
                }
            }
            _ => {}
        }
    }
}

/// A sub-table: its header, if it needs one, then its body.
fn write_table<'a>(
    out: &mut String,
    path: &mut Vec<&'a str>,
    entries: &'a [(String, Node)],
    style: Style,
) {
    // An empty table has no other evidence of its existence, so it must be
    // declared. A table with at least one `key = value` entry must be declared
    // so those lines have somewhere to live. A table holding nothing but child
    // blocks needs no header — see the module docs.
    if entries.is_empty() || entries.iter().any(|(_, node)| node.is_inline_entry()) {
        write_header(out, path, false);
    }
    write_body(out, path, entries, style);
}

fn write_header(out: &mut String, path: &[&str], array: bool) {
    // A blank line before every block except the first thing in the document.
    // Matches the incumbent, measured.
    if !out.is_empty() {
        out.push('\n');
    }
    let joined =
        path.iter().map(|part| render_key(part)).collect::<Vec<_>>().join(".");
    let _ = if array {
        writeln!(out, "[[{joined}]]")
    } else {
        writeln!(out, "[{joined}]")
    };
}

/// A value in `key = value` position, inside an array, or inside an inline
/// table.
///
/// `depth` counts the enclosing arrays that have been **broken** across lines,
/// not the enclosing arrays. That distinction is measured: `k = [[1, 2]]` under
/// `to_string_pretty` renders as `[[` / `    1,` / `    2,` / `]]` — the outer
/// array has one element so it stays inline and contributes no indent, while the
/// inner array breaks and indents by one level.
fn render_inline(node: &Node, style: Style, depth: usize) -> String {
    match node {
        Node::String(value) => render_string(value),
        Node::Integer(value) => value.to_string(),
        Node::Float(value) => render_float(*value),
        Node::Boolean(value) => value.to_string(),
        Node::Datetime(text) => text.clone(),
        Node::Array(items) => render_array(items, style, depth),
        Node::Table(entries) => {
            // Reachable only for a table nested inside an array, since a table
            // in table-entry position is written as a `[header]` block.
            if entries.is_empty() {
                return "{}".to_string();
            }
            let rendered: Vec<String> = entries
                .iter()
                .map(|(key, value)| {
                    format!("{} = {}", render_key(key), render_inline(value, style, depth))
                })
                .collect();
            format!("{{ {} }}", rendered.join(", "))
        }
    }
}

fn render_array(items: &[Node], style: Style, depth: usize) -> String {
    if style == Style::Pretty && items.len() >= 2 {
        let inner = "    ".repeat(depth + 1);
        let outer = "    ".repeat(depth);
        let mut out = String::from("[\n");
        for item in items {
            let _ = writeln!(out, "{inner}{},", render_inline(item, style, depth + 1));
        }
        let _ = write!(out, "{outer}]");
        return out;
    }
    let rendered: Vec<String> =
        items.iter().map(|item| render_inline(item, style, depth)).collect();
    format!("[{}]", rendered.join(", "))
}

/// A key: bare when it provably can be, quoted otherwise.
///
/// The bare-key predicate is [`is_bare_key_byte`], the *same* function the
/// parser uses to read one. Sharing it is the point: a writer and a reader that
/// each carry their own copy of "what a bare key looks like" will eventually
/// disagree, and the failure is a document this crate writes and cannot read.
pub(crate) fn render_key(key: &str) -> String {
    if !key.is_empty() && key.bytes().all(is_bare_key_byte) {
        key.to_string()
    } else {
        // Single-line: TOML has no multi-line key. Measured, the incumbent
        // writes the key `a\nb` as `"a\nb"` even though it writes the *value*
        // `a\nb` as a `"""` block.
        render_string_oneline(key)
    }
}

/// Which of TOML's four string spellings to use.
///
/// TOML can write the same string four ways, and the incumbent picks between
/// them. The rule below was **derived from measurement**, not from reading
/// `toml_edit`: twenty-eight adversarial strings were put through
/// `toml 0.8.23`'s emitter, the rule was fitted to the results, and it is now
/// pinned by
/// `tests/serialize_differential.rs::string_spelling_matches_the_incumbent_over_generated_strings`,
/// which re-derives the comparison over thousands of generated strings on every
/// run. A heuristic copied by eye rots silently; one pinned by a differential
/// cannot.
///
/// # The rule
///
/// Minimise the number of characters that must be **escaped**, counting only
/// `"` and `\` — the two a basic string escapes and a literal string writes
/// free. Break ties by preferring one line over three, then basic over literal.
/// A string containing a newline is never written on one line.
///
/// The tie-breaks are what make the rule non-obvious, and each is measured:
/// `a"b` becomes `'a"b'` (one-line literal beats multi-line basic, both
/// escape-free), while `a"b'c` becomes a multi-line basic string (the one-line
/// literal is impossible there, and basic beats literal at equal cost).
///
/// # Why this is worth reproducing at all
///
/// An earlier draft of this module always wrote a one-line basic string, on the
/// reasoning that the acceptance gate measures value preservation and every
/// spelling preserves the value. That reasoning was right and the decision was
/// wrong: `tests/js262/divergence-audit.toml` — a 23,000-line ledger this
/// repository's own tooling rewrites — contains a `reason` string holding both
/// a `"` and a `'`, so the simple rule reprinted it with escapes and turned a
/// no-op regeneration into a diff on every entry. Cosmetic differences are
/// cheap right up until they land in a reviewed file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringForm {
    Basic,
    Literal,
    MultilineBasic,
    MultilineLiteral,
}

/// The escapes a basic string needs and a literal string does not. This is the
/// cost the choice minimises. A control character is deliberately **not**
/// counted: a control forces a basic string outright rather than tipping a
/// preference (measured: `a\tb` becomes `"a\tb"`, not a literal string holding a
/// raw tab).
fn basic_escape_cost(value: &str) -> usize {
    value.chars().filter(|character| *character == '"' || *character == '\\').count()
}

/// A literal string escapes nothing, so it can hold nothing that needs
/// escaping: TOML forbids every control character except tab, and DEL.
fn literal_char_ok(character: char) -> bool {
    character == '\t' || (character >= '\u{20}' && character != '\u{7f}')
}

fn oneline_literal_valid(value: &str) -> bool {
    !value.contains('\'') && value.chars().all(literal_char_ok)
}

fn multiline_literal_valid(value: &str) -> bool {
    !value.contains("'''")
        && !value.ends_with('\'')
        && value.chars().all(|character| character == '\n' || literal_char_ok(character))
}

/// How many `"` a multi-line basic string has to escape: **one per run of
/// three**, and no others.
///
/// Two counter-intuitive facts, both measured against `toml 0.8.23`, and both
/// found by a differential rather than by reading the spec carefully enough:
///
/// * A **trailing** quote needs no escape. TOML terminates a multi-line basic
///   string at the *last* `"""` of a quote run, so the value `a"` is written
///   `"""a""""` — four quotes, the first of which is content. An earlier draft
///   escaped a trailing quote defensively, which pushed every such value into a
///   literal string and disagreed with the incumbent on a whole family.
/// * A run of three is broken by escaping **only the third**: `"""` inside the
///   content is written `""\"`, not `\"\"\"`. Escaping all three also parses,
///   and is also three characters longer per run.
///
/// The count and the rendering are derived from one walk each over the same
/// rule, so the cost model and [`escape_into`] cannot disagree about how many
/// escapes there will be.
fn multiline_basic_quote_escapes(value: &str) -> usize {
    let mut run = 0usize;
    let mut escapes = 0usize;
    for character in value.chars() {
        if character == '"' {
            run += 1;
            if run == 3 {
                escapes += 1;
                run = 0;
            }
        } else {
            run = 0;
        }
    }
    escapes
}

fn multiline_basic_cost(value: &str) -> usize {
    value.chars().filter(|character| *character == '\\').count()
        + multiline_basic_quote_escapes(value)
}

/// `multiline` is false in **key** position, which TOML requires to be a
/// single-line string. Measured: the key `a\nb` is written `"a\nb"`, never as a
/// `"""` block.
fn choose_form(value: &str, multiline: bool) -> StringForm {
    if !value.contains('\n') {
        if basic_escape_cost(value) == 0 {
            return StringForm::Basic;
        }
        if oneline_literal_valid(value) {
            return StringForm::Literal;
        }
        // The one-line literal is unavailable. Whether to escalate to a `"""`
        // block depends on WHY, and this is measured: the incumbent escalates
        // when an apostrophe blocked the literal (`a"b'c` becomes
        // `"""a"b'c"""`) but not when a control character did (`"` followed by
        // a carriage return stays `"\"\r"`). A control character forces escaping
        // regardless of delimiter, so a bigger delimiter buys nothing and the
        // one-line basic string is simply the shortest correct answer.
        if !multiline || !value.chars().all(literal_char_ok) {
            return StringForm::Basic;
        }
    } else if !multiline {
        return StringForm::Basic;
    }
    if multiline_basic_cost(value) == 0 {
        return StringForm::MultilineBasic;
    }
    if multiline_literal_valid(value) {
        return StringForm::MultilineLiteral;
    }
    // Every escape-free option is unavailable. A basic string can represent
    // anything, so it is the total fallback — multi-line only when the value
    // contains a newline, which a one-line string would have to escape.
    if value.contains('\n') { StringForm::MultilineBasic } else { StringForm::Basic }
}

/// A string, in whichever of TOML's four spellings the incumbent would choose.
/// See [`StringForm`].
fn render_string(value: &str) -> String {
    render_string_with(value, true)
}

/// A single-line string, for key position. See [`choose_form`].
fn render_string_oneline(value: &str) -> String {
    render_string_with(value, false)
}

fn render_string_with(value: &str, multiline: bool) -> String {
    match choose_form(value, multiline) {
        StringForm::Basic => {
            let mut out = String::with_capacity(value.len() + 2);
            out.push('"');
            escape_into(&mut out, value, false);
            out.push('"');
            out
        }
        StringForm::Literal => format!("'{value}'"),
        StringForm::MultilineBasic => {
            let mut out = String::with_capacity(value.len() + 8);
            out.push_str("\"\"\"");
            out.push_str(opening_newline(value));
            escape_into(&mut out, value, true);
            out.push_str("\"\"\"");
            out
        }
        StringForm::MultilineLiteral => {
            format!("'''{}{value}'''", opening_newline(value))
        }
    }
}

/// The newline that follows the opening `"""` or `'''`, if any.
///
/// TOML trims a newline immediately after the opening delimiter, so it is
/// formatting rather than content and either choice is correct. The incumbent
/// emits it **only when the value itself contains a newline** — measured: the
/// value `a\nb` becomes `"""` + newline + `a` + newline + `b"""`, while the
/// single-line value `a"b'c`, which is also written as a `"""` block because it
/// holds both quote characters, becomes `"""a"b'c"""` with no break at all.
/// Getting this wrong is invisible to a round-trip test and shows up as a
/// one-line diff on every string in a regenerated ledger.
fn opening_newline(value: &str) -> &'static str {
    if value.contains('\n') { "\n" } else { "" }
}

/// The basic-string escape set, exactly TOML v1.0.0's.
///
/// `multiline` changes exactly two characters. A newline is written raw (that is
/// the point of the form), and a `"` is escaped only when it is the third of a
/// run — see [`multiline_basic_quote_escapes`] for why, and note that the count
/// there and the emission here walk the same rule. Everything else is identical
/// in both forms: `\`, the five short escapes, and `\uXXXX` — four digits,
/// upper-case hex, measured — for every other C0 control and for DEL. Tab is
/// escaped even though a raw tab is legal, matching the incumbent and keeping
/// the output free of characters a diff renders ambiguously. All non-ASCII
/// passes through unescaped, also matching the incumbent (measured: an accented
/// word and an arrow both survive verbatim).
fn escape_into(out: &mut String, value: &str, multiline: bool) {
    let mut quote_run = 0usize;
    for character in value.chars() {
        if character == '"' {
            quote_run += 1;
        } else {
            quote_run = 0;
        }
        match character {
            '"' if !multiline => out.push_str("\\\""),
            '"' if quote_run == 3 => {
                out.push_str("\\\"");
                quote_run = 0;
            }
            '"' => out.push('"'),
            '\n' if multiline => out.push('\n'),
            '\\' => out.push_str("\\\\"),
            '\u{8}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            control if control < '\u{20}' || control == '\u{7f}' => {
                let _ = write!(out, "\\u{:04X}", control as u32);
            }
            other => out.push(other),
        }
    }
}

/// A float, in a spelling that reads back as a **float**.
///
/// The trap this function exists for: `format!("{}", 1.0_f64)` is `"1"`, and
/// `1` in a TOML document is an *integer*. Emitting it would silently change the
/// type of the value across a round trip, and would do so only for floats that
/// happen to be integral — the classic "works in every test, fails on the one
/// config that says `1.0`" defect. So a rendering with no `.` and no exponent
/// gets `.0` appended.
///
/// Rust's `Display` for `f64` prints the shortest decimal that round-trips and
/// never uses exponent notation, so `1e300` comes out as 301 digits. That is
/// also what the incumbent emits, measured, so the two agree without any
/// special handling. `-0.0` renders as `-0.0`, preserving the sign bit, which is
/// observable once the value is re-emitted or digested.
///
/// `inf`, `-inf` and `nan` are TOML v1.0.0 literals and are emitted as such,
/// again matching the incumbent. Note that a negative NaN is written `nan`, not
/// `-nan`: TOML permits both spellings, NaN's sign is not semantically
/// meaningful, and this matches the incumbent.
///
/// # The corpus differential cannot see this function, and that is measured
///
/// Exactly **1 of the 1,381 pinned corpus documents contains a float at all,
/// and none contains an integral-valued one**. So deleting the `.0` above
/// changes nothing the corpus differential compares — verified by mutation: the
/// suite's only failure was `floats_never_lose_their_floatness`, which is
/// therefore the *sole* evidence for this rule rather than a convenience
/// duplicate of a bigger gate. Do not delete it on the grounds that "the
/// differential covers it".
fn render_float(value: f64) -> String {
    if value.is_nan() {
        return "nan".to_string();
    }
    if value.is_infinite() {
        return if value.is_sign_positive() { "inf".to_string() } else { "-inf".to_string() };
    }
    let mut rendered = format!("{value}");
    if !rendered.contains(['.', 'e', 'E']) {
        rendered.push_str(".0");
    }
    rendered
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table(entries: &[(&str, Node)]) -> Vec<(String, Node)> {
        entries.iter().map(|(key, node)| ((*key).to_string(), node.clone())).collect()
    }

    fn int(value: i64) -> Node {
        Node::Integer(value)
    }

    #[test]
    fn values_are_written_before_sub_tables() {
        // The rule this crate exists to get right. If `sub` were written first,
        // `scalar = 1` would land INSIDE `[sub]` and the document would parse.
        let doc = document(
            &table(&[
                ("sub", Node::Table(table(&[("inner", int(2))]))),
                ("scalar", int(1)),
            ]),
            Style::Compact,
        );
        assert_eq!(doc, "scalar = 1\n\n[sub]\ninner = 2\n");
    }

    #[test]
    fn a_table_of_only_tables_gets_no_header_but_an_empty_one_does() {
        let deep = Node::Table(table(&[(
            "b",
            Node::Table(table(&[("c", Node::Table(table(&[("x", int(1))])))])),
        )]));
        assert_eq!(document(&table(&[("a", deep)]), Style::Compact), "[a.b.c]\nx = 1\n");
        assert_eq!(
            document(&table(&[("sub", Node::Table(Vec::new()))]), Style::Compact),
            "[sub]\n"
        );
    }

    #[test]
    fn an_array_of_tables_is_blocks_but_an_empty_one_is_an_inline_array() {
        let entries = Node::Array(vec![
            Node::Table(table(&[("a", int(1))])),
            Node::Table(table(&[("a", int(2))])),
        ]);
        assert_eq!(
            document(&table(&[("e", entries)]), Style::Compact),
            "[[e]]\na = 1\n\n[[e]]\na = 2\n"
        );
        // An empty array of tables has no tables to write blocks for. Written as
        // blocks it would disappear; written inline it survives.
        assert_eq!(
            document(&table(&[("e", Node::Array(Vec::new()))]), Style::Compact),
            "e = []\n"
        );
    }

    #[test]
    fn a_sub_table_of_an_array_element_is_headed_by_the_key_not_the_index() {
        // `[entries.expectation]`, not `[entries[0].expectation]`. This is the
        // shape `tests/js262/baseline.toml` is written in.
        let element = Node::Table(table(&[
            ("id", Node::String("x".to_string())),
            ("expectation", Node::Table(table(&[("rule", int(1))]))),
        ]));
        assert_eq!(
            document(&table(&[("entries", Node::Array(vec![element]))]), Style::Compact),
            "[[entries]]\nid = \"x\"\n\n[entries.expectation]\nrule = 1\n"
        );
    }

    #[test]
    fn a_key_that_is_not_bare_is_quoted_in_both_entry_and_header_position() {
        // Unquoted, `a.b` would be a DOTTED key and would mean `{a: {b: 1}}`.
        assert_eq!(render_key("a.b"), "\"a.b\"");
        assert_eq!(render_key(""), "\"\"");
        assert_eq!(render_key("a b"), "\"a b\"");
        assert_eq!(render_key("é"), "\"é\"");
        assert_eq!(render_key("A-b_9"), "A-b_9");
        assert_eq!(render_key("1"), "1");
        assert_eq!(
            document(&table(&[("a.b", Node::Table(table(&[("x", int(1))])))]), Style::Compact),
            "[\"a.b\"]\nx = 1\n"
        );
    }

    #[test]
    fn floats_never_lose_their_floatness() {
        // The whole reason `render_float` exists.
        assert_eq!(render_float(1.0), "1.0");
        assert_eq!(render_float(-0.0), "-0.0");
        assert_eq!(render_float(0.5), "0.5");
        assert_eq!(render_float(f64::INFINITY), "inf");
        assert_eq!(render_float(f64::NEG_INFINITY), "-inf");
        assert_eq!(render_float(f64::NAN), "nan");
        assert_eq!(render_float(-f64::NAN), "nan");
    }

    /// Every expectation below is a **measurement** of `toml 0.8.23`, taken by
    /// running its emitter over these exact inputs. They are asserted here as
    /// well as in the generated differential because a unit test names the case
    /// — `a\b'c` is here because it is the one that forces a multi-line literal
    /// string, and that is worth being able to read.
    #[test]
    fn strings_are_spelled_the_way_the_incumbent_spells_them() {
        // Nothing to escape: a plain one-line basic string.
        assert_eq!(render_string("plain"), "\"plain\"");
        assert_eq!(render_string(""), "\"\"");
        assert_eq!(render_string("héllo→"), "\"héllo→\"");
        // An apostrophe needs no escape in a basic string, so it stays basic.
        assert_eq!(render_string("a'b"), "\"a'b\"");

        // A quote or a backslash would need escaping, and a literal string
        // spells both free.
        assert_eq!(render_string("a\"b"), "'a\"b'");
        assert_eq!(render_string("a\\b"), "'a\\b'");
        assert_eq!(render_string("a\"\"\"b"), "'a\"\"\"b'");

        // A newline forces a multi-line form, and then basic beats literal at
        // equal cost — but a backslash tips it to literal.
        assert_eq!(render_string("a\nb"), "\"\"\"\na\nb\"\"\"");
        assert_eq!(render_string("a\\\nb"), "'''\na\\\nb'''");
        // A carriage return must be escaped, which a literal string cannot do.
        assert_eq!(render_string("a\r\nb"), "\"\"\"\na\\r\nb\"\"\"");

        // Both quote characters: the one-line literal is impossible, so it
        // escalates to a multi-line form — with NO opening newline, because the
        // value has none.
        assert_eq!(render_string("a\"b'c"), "\"\"\"a\"b'c\"\"\"");
        assert_eq!(render_string("a\\b'c"), "'''a\\b'c'''");

        // A control character forces a basic string and blocks the escalation:
        // a bigger delimiter cannot help, so the shortest correct answer wins.
        assert_eq!(render_string("a\tb"), "\"a\\tb\"");
        assert_eq!(render_string("a\rb"), "\"a\\rb\"");
        assert_eq!(render_string("a\u{8}b"), "\"a\\bb\"");
        assert_eq!(render_string("a\u{c}b"), "\"a\\fb\"");
        assert_eq!(render_string("a\u{1}b"), "\"a\\u0001b\"");
        assert_eq!(render_string("a\u{7f}b"), "\"a\\u007Fb\"");
        assert_eq!(render_string("\"\r"), "\"\\\"\\r\"");

        // A trailing quote inside `"""` is NOT escaped: TOML closes the string
        // at the last `"""` of a run, so this is four quotes of which one is
        // content.
        assert_eq!(render_string("a\n\""), "\"\"\"\na\n\"\"\"\"");
        // Inside `"""`, only the THIRD quote of a run is escaped. Reaching this
        // arm needs a value that ALSO blocks the multi-line literal, which a
        // control character does — this exact case came out of the generated
        // differential, which is why it is written down rather than invented.
        assert_eq!(
            render_string("\u{2192}\"\"\"\u{7f}\r\n.{"),
            "\"\"\"\n\u{2192}\"\"\\\"\\u007F\\r\n.{\"\"\""
        );

        // A key is never multi-line, whatever the value rule would do.
        assert_eq!(render_string_oneline("a\nb"), "\"a\\nb\"");
        assert_eq!(render_string_oneline("a\"b"), "'a\"b'");
    }

    #[test]
    fn pretty_breaks_arrays_of_two_or_more_and_indents_by_broken_depth() {
        let two = Node::Array(vec![int(1), int(2)]);
        assert_eq!(
            document(&table(&[("k", two.clone())]), Style::Pretty),
            "k = [\n    1,\n    2,\n]\n"
        );
        // Length 0 and 1 stay inline in both styles.
        assert_eq!(document(&table(&[("k", Node::Array(vec![int(1)]))]), Style::Pretty), "k = [1]\n");
        assert_eq!(document(&table(&[("k", Node::Array(vec![]))]), Style::Pretty), "k = []\n");
        // The outer array does not break, so it adds no indent level.
        assert_eq!(
            document(&table(&[("k", Node::Array(vec![two.clone()]))]), Style::Pretty),
            "k = [[\n    1,\n    2,\n]]\n"
        );
        // Compact leaves every array on one line.
        assert_eq!(document(&table(&[("k", two)]), Style::Compact), "k = [1, 2]\n");
    }

    #[test]
    fn a_table_inside_an_array_is_written_inline() {
        let mixed = Node::Array(vec![Node::Table(table(&[("k", int(1))])), int(2)]);
        assert_eq!(
            document(&table(&[("m", mixed)]), Style::Compact),
            "m = [{ k = 1 }, 2]\n"
        );
        let empty_inline = Node::Array(vec![Node::Table(Vec::new()), int(2)]);
        assert_eq!(document(&table(&[("m", empty_inline)]), Style::Compact), "m = [{}, 2]\n");
    }

    #[test]
    fn an_empty_document_is_the_empty_string() {
        assert_eq!(document(&[], Style::Compact), "");
    }
}
