// Unit tests for the stable obligation key (T9): the token reading, every anchor
// class, `nth` ordering and twins, the refused collision, and that no position
// enters a key.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

fn span(line_start: u32, col_start: u32, line_end: u32, col_end: u32) -> SourceSpan {
    SourceSpan { file: "src/lib.rs".to_string(), line_start, col_start, line_end, col_end }
}

const SOURCE: &str = "pub fn f(a: u64, b: u64) -> u64 {\n    let x = a / b;\n    a + b + x\n}\n";

fn local(span: &SourceSpan) -> String {
    let lines = LineIndex::new(SOURCE);
    anchor(AnchorInput::Local { span, text: SOURCE, lines: &lines }).expect("anchor")
}

fn kd(kind: &'static str, anchor: &'static str, position: SpanPosition) -> KeyedRow<'static> {
    KeyedRow { kind, anchor, position, discriminator: "" }
}

#[test]
fn the_token_reading_drops_whitespace_and_comments_only() {
    assert_eq!(token_text("a/b"), "a / b");
    assert_eq!(token_text("f(a,b)"), token_text("f(a, b)"));
    assert_eq!(token_text("foo(\n    a,\n)"), "foo ( a , )");
    assert_eq!(token_text("x /* a /* nested */ comment */ + 1 // tail\n"), "x + 1");
    assert_eq!(token_text("/// doc\nfn f() {}"), "fn f ( ) { }");
    // Literals are content, whitespace and comment markers inside them included.
    assert_eq!(token_text(r#"s("a  // b", 'c', b'd')"#), r#"s ( "a  // b" , 'c' , b'd' )"#);
    assert_ne!(token_text(r#""a  b""#), token_text(r#""a b""#));
    assert_eq!(token_text(r###"r#"x " y"#.len()"###), r###"r#"x " y"# . len ( )"###);
    assert_eq!(token_text(r#"c"z" br"q""#), r#"c"z" br"q""#);
    assert_eq!(token_text(r#""\"q\"" + 1"#), r#""\"q\"" + 1"#);
    // Lifetimes, labels and escaped character literals.
    assert_eq!(
        token_text("fn f<'a>(x: &'a u8) -> char { '\\'' }"),
        "fn f < 'a > ( x : & 'a u8 ) - > char { '\\'' }"
    );
    assert_eq!(token_text("'outer: loop { break 'outer; }"), "'outer : loop { break 'outer ; }");
    // Numbers, raw identifiers.
    assert_eq!(token_text("1.5e-3f64+0x1F_u8..2"), "1.5e-3f64 + 0x1F_u8 . . 2");
    assert_eq!(token_text("r#type + t.0.1"), "r#type + t . 0.1");
    // Unterminated literals and comments run to the end rather than failing.
    assert_eq!(tokens("\"open").len(), 1);
    assert_eq!(tokens("x /* open").len(), 1);
}

#[test]
fn a_local_span_anchors_on_the_statement_around_its_start() {
    // `a / b` on line 2 anchors on its statement, `let x = a / b`.
    let anchor = local(&span(2, 12, 2, 17));
    assert_eq!(anchor, format!("stmt:{}", sha16(b"let x = a / b")));
    // The same tokens with other spacing, a line break and a comment are the
    // same anchor: a reformat is not an edit.
    let wide = "pub fn f() {\n    let x = a/* why */  /\n  b;\n}\n";
    let lines = LineIndex::new(wide);
    let wide_anchor =
        super::anchor(AnchorInput::Local { span: &span(2, 12, 3, 3), text: wide, lines: &lines })
            .expect("anchor");
    assert_eq!(wide_anchor, anchor);
    let tight = "pub fn f() {\n    let x = a/b;\n}\n";
    let lines = LineIndex::new(tight);
    let tight_anchor =
        super::anchor(AnchorInput::Local { span: &span(2, 12, 2, 15), text: tight, lines: &lines })
            .expect("anchor");
    assert_eq!(tight_anchor, anchor);
}

#[test]
fn a_point_and_a_range_of_one_obligation_share_anchor_and_position() {
    // The END is not the obligation's: one compile publishes this division as
    // the point at `a`, another as the range `a / b` (measured 2026-10-10,
    // `tests/run-make/trust-obligation-ids`). Both are one obligation, so both
    // mint one key.
    let point = span(2, 12, 2, 12);
    let range = span(2, 12, 2, 17);
    assert_eq!(local(&point), local(&range));
    assert_eq!(span_position(Some(&point)), span_position(Some(&range)));
    let row = |position| KeyedRow {
        kind: "divzero",
        anchor: "stmt:aa",
        position,
        discriminator: "division by zero",
    };
    // Twins published as two ranges of different ends, `y + a` and `y + a + z`,
    // or as two points at their common start, are ordered the same way.
    let ranges =
        [row(span_position(Some(&span(3, 4, 3, 9)))), row(span_position(Some(&span(3, 4, 3, 13))))];
    let points =
        [row(span_position(Some(&span(3, 4, 3, 4)))), row(span_position(Some(&span(3, 4, 3, 4))))];
    assert_eq!(local_ids(&ranges).expect("ids"), local_ids(&points).expect("ids"));
}

#[test]
fn a_point_span_anchors_on_its_statement() {
    let anchor = local(&span(3, 4, 3, 4));
    assert_eq!(anchor, format!("stmt:{}", sha16(b"a + b + x")));
    // A reflow of the statement over three lines keeps the anchor, and so does
    // an edit of another statement on the same line.
    let reflowed =
        "pub fn f(a: u64, b: u64) -> u64 {\n    let x = a / b; a\n        + b\n        + x\n}\n";
    let lines = LineIndex::new(reflowed);
    let point = span(2, 19, 2, 19);
    assert_eq!(lines.span_text(reflowed, &span(2, 19, 2, 20)), Some("a"));
    assert_eq!(
        super::anchor(AnchorInput::Local { span: &point, text: reflowed, lines: &lines }),
        Ok(anchor.clone())
    );
    let other = "pub fn f(a: u64, b: u64) -> u64 {\n    let x = a / (b | 1); a + b + x\n}\n";
    let lines = LineIndex::new(other);
    let point = span(2, 25, 2, 25);
    assert_eq!(
        super::anchor(AnchorInput::Local { span: &point, text: other, lines: &lines }),
        Ok(anchor)
    );
}

#[test]
fn a_statement_is_read_lexically() {
    let statement = |text: &str, at: &str| -> String {
        let all = tokens(text);
        let offset = text.find(at).expect("the marker is in the text");
        let point = all.partition_point(|&(_, end)| end <= offset);
        let (first, last) = statement_tokens(text, &all, point);
        join_tokens(text, &all[first..last])
    };
    // Inside a call's arguments: the whole call statement.
    let text = "fn f() { g(); v.iter().map(|x| x + 1).sum(); h(); }";
    assert_eq!(statement(text, "x + 1"), "v . iter ( ) . map ( | x | x + 1 ) . sum ( )");
    // A condition does not take its block along; the block's statement stands alone.
    let text = "fn f() { if a + b > c { d * e; } }";
    assert_eq!(statement(text, "a + b"), "if a + b > c");
    assert_eq!(statement(text, "d * e"), "d * e");
    // A match arm stands alone.
    let text = "fn f() { match v { A => a + b, B => c + d } }";
    assert_eq!(statement(text, "c + d"), "B = > c + d");
    // A macro call at its callsite.
    let text = "fn f() {\n    halve!(a, d)\n}";
    assert_eq!(statement(text, "halve"), "halve ! ( a , d )");
    // A point past the last token is the empty statement.
    let all = tokens("x");
    assert_eq!(statement_tokens("x", &all, 1), (1, 1));
}

#[test]
fn an_external_span_anchors_on_its_normalized_path_with_no_position() {
    let first =
        anchor(AnchorInput::External { file: "/rustc/<toolchain>/library/core/src/num/mod.rs" })
            .expect("anchor");
    assert_eq!(first, "ext:@sysroot/library/core/src/num/mod.rs");
    assert_eq!(
        normalize_external_path(
            "<cargo-home>/registry/src/index.crates.io-1949cf8c6b5b557f/serde-1.0.0/src/de.rs"
        ),
        "@registry/serde-1.0.0/src/de.rs"
    );
    assert_eq!(
        normalize_external_path(
            "/home/a/.cargo/git/checkouts/foo-0123456789abcdef/1a2b3c4/src/lib.rs"
        ),
        "@git/src/lib.rs"
    );
    assert_eq!(
        normalize_external_path("<home>/ws/vendor/astream/crates/astream-wire/src/lib.rs"),
        "@crate/astream-wire/src/lib.rs"
    );
    // Two checkouts of the same path dependency agree.
    assert_eq!(
        normalize_external_path("<home>/elsewhere/astream-wire/src/lib.rs"),
        normalize_external_path("<home>/ws/vendor/astream/crates/astream-wire/src/lib.rs")
    );
    assert_eq!(normalize_external_path("crates/x/src/lib.rs"), "@crate/crates/x/src/lib.rs");
    assert_eq!(
        normalize_external_path("/opt/trust/lib/rustlib/src/rust/library/alloc/src/vec/mod.rs"),
        "@sysroot/library/alloc/src/vec/mod.rs"
    );
}

#[test]
fn an_unlocated_row_anchors_on_its_normalized_description() {
    let a = anchor(AnchorInput::Unlocated { description: "assume  _12 holds at bb3 @deadbeef01" })
        .expect("anchor");
    let b = anchor(AnchorInput::Unlocated { description: "assume _7 holds at bb3 @0123456789ab" })
        .expect("anchor");
    assert_eq!(a, b, "MIR locals and hash suffixes are not identity");
    assert!(a.starts_with("none:"));
    assert_eq!(normalize_description("_3#s0_1 + x_2"), "_#s0_1 + x_2");
    assert_eq!(normalize_description("call @abc"), "call @abc", "short hex is kept");
}

#[test]
fn the_input_constructor_routes_each_row_class() {
    let lines = LineIndex::new(SOURCE);
    let located = span(2, 12, 2, 17);
    assert!(matches!(
        AnchorInput::of(None, "d", Some((SOURCE, &lines))),
        AnchorInput::Unlocated { .. }
    ));
    assert!(matches!(
        AnchorInput::of(Some(&SourceSpan::default()), "d", None),
        AnchorInput::Unlocated { .. }
    ));
    assert!(matches!(AnchorInput::of(Some(&located), "d", None), AnchorInput::External { .. }));
    assert!(matches!(
        AnchorInput::of(Some(&located), "d", Some((SOURCE, &lines))),
        AnchorInput::Local { .. }
    ));
}

#[test]
fn a_span_outside_its_text_is_refused() {
    let lines = LineIndex::new(SOURCE);
    // The last: a start past the last token, which no statement lies around.
    for bad in [span(9, 0, 9, 1), span(2, 0, 2, 99), span(2, 10, 2, 5), span(5, 0, 5, 0)] {
        assert!(
            anchor(AnchorInput::Local { span: &bad, text: SOURCE, lines: &lines }).is_err(),
            "{bad:?}"
        );
    }
}

#[test]
fn the_compiler_anchor_degrades_instead_of_refusing() {
    let lines = LineIndex::new(SOURCE);
    // A span whose end lies past its line: its start line anchors it.
    let past = span(2, 0, 2, 99);
    assert_eq!(
        row_anchor(AnchorInput::Local { span: &past, text: SOURCE, lines: &lines }),
        RowAnchor { anchor: format!("line:{}", sha16(b"let x = a / b ;")), degraded: true }
    );
    // A span that covers no token (only whitespace) is degraded the same way.
    let blank = span(2, 0, 2, 4);
    assert!(anchor(AnchorInput::Local { span: &blank, text: SOURCE, lines: &lines }).is_err());
    assert!(row_anchor(AnchorInput::Local { span: &blank, text: SOURCE, lines: &lines }).degraded);
    // A span whose start line does not exist: its file anchors it.
    let gone = span(9, 0, 9, 1);
    assert_eq!(
        row_anchor(AnchorInput::Local { span: &gone, text: SOURCE, lines: &lines }),
        RowAnchor { anchor: "ext:@crate/src/lib.rs".to_string(), degraded: true }
    );
    // A well-formed span anchors exactly as `anchor` does, undegraded.
    let good = span(2, 12, 2, 17);
    assert_eq!(
        row_anchor(AnchorInput::Local { span: &good, text: SOURCE, lines: &lines }),
        RowAnchor { anchor: local(&good), degraded: false }
    );
}

#[test]
fn character_columns_are_not_byte_columns() {
    let text = "fn f() { let s = \"é\"; s.len() / 0 }\n";
    let lines = LineIndex::new(text);
    // `s.len() / 0` starts at char 22 (byte 23: `é` is two bytes).
    let div = span(1, 22, 1, 33);
    assert_eq!(lines.span_text(text, &div), Some("s.len() / 0"));
}

#[test]
fn nth_counts_rows_with_the_same_kind_and_anchor_in_span_order() {
    let rows = [
        kd("divzero", "stmt:aa", (5, 0)),
        kd("divzero", "stmt:aa", (2, 0)),
        kd("overflow:add", "stmt:aa", (2, 0)),
    ];
    let ids = local_ids(&rows).expect("ids");
    assert_eq!(ids[1], local_id("divzero", "stmt:aa", 0), "the earlier span is nth 0");
    assert_eq!(ids[0], local_id("divzero", "stmt:aa", 1));
    assert_eq!(ids[2], local_id("overflow:add", "stmt:aa", 0), "another kind counts on its own");
}

#[test]
fn same_span_twins_are_ordered_by_emission_and_disambiguated() {
    let twin = kd("divzero", "stmt:bb", (7, 4));
    let ids = local_ids(&[twin, twin]).expect("ids");
    assert_ne!(ids[0], ids[1]);
    assert_eq!(ids[0], local_id("divzero", "stmt:bb", 0));
    assert_eq!(ids[1], local_id("divzero", "stmt:bb", 1));
}

#[test]
fn twins_with_different_content_keep_their_keys_in_any_emission_order() {
    // Two rows with one kind, anchor and position, told apart by their
    // descriptions: whichever the compiler emits first, each keeps its key.
    let x = row_discriminator("division by zero: `_4 / _5`");
    let y = row_discriminator("remainder by zero: `_4 % _5`");
    let row = |discriminator: &'static str| KeyedRow {
        kind: "divzero",
        anchor: "stmt:bb",
        position: (7, 4),
        discriminator,
    };
    let (x, y): (&'static str, &'static str) = (x.leak(), y.leak());
    let forward = local_ids(&[row(x), row(y)]).expect("ids");
    let backward = local_ids(&[row(y), row(x)]).expect("ids");
    assert_eq!(forward[0], backward[1], "x keeps its key");
    assert_eq!(forward[1], backward[0], "y keeps its key");
    // MIR locals are not content.
    assert_eq!(row_discriminator("a `_4 / _5`"), row_discriminator("a `_7 / _2`"));
}

#[test]
fn removing_a_row_renumbers_only_its_own_cell() {
    let rows = [
        kd("slice", "stmt:01", (1, 0)),
        kd("divzero", "stmt:02", (1, 0)),
        kd("postcond", "stmt:03", (1, 0)),
        kd("divzero", "stmt:02", (1, 0)),
    ];
    let all = local_ids(&rows).expect("ids");
    // The ordinal mint renumbered everything after a removed row; here dropping
    // the slice row leaves every other key alone.
    let without_slice = local_ids(&rows[1..]).expect("ids");
    assert_eq!(&all[1..], without_slice.as_slice());
}

#[test]
fn key_derivation_reads_no_position_beyond_the_order() {
    // The same rows shifted down twenty lines (an edit above the function) keep
    // their ids: only relative order enters, through `nth`.
    let rows = |shift: u32| {
        [kd("divzero", "stmt:cc", (3 + shift, 4)), kd("divzero", "stmt:cc", (9 + shift, 4))]
    };
    assert_eq!(local_ids(&rows(0)).unwrap(), local_ids(&rows(20)).unwrap());
}

#[test]
fn a_forced_collision_fails_closed() {
    let rows = [kd("slice", "stmt:aa", (1, 0)), kd("divzero", "stmt:bb", (2, 0))];
    let collision = mint_local_ids(&rows, |_, _, _| "0123456789abcdef".to_string())
        .expect_err("a colliding mint must be refused");
    assert_eq!(collision, IdCollision { id: "0123456789abcdef".to_string(), rows: (0, 1) });
    assert!(collision.to_string().contains("no row of this function carries a stable key"));
}

#[test]
fn keys_split_at_the_last_separator_and_validate_the_id() {
    let id = local_id("divzero", "stmt:aa", 0);
    let key = obligation_key("c::f::{closure#0}", &id);
    assert_eq!(split_obligation_key(&key), Some(("c::f::{closure#0}", id.as_str())));
    assert_eq!(split_obligation_key("c::f#XYZ"), None);
    assert_eq!(split_obligation_key("#0123456789abcdef"), None);
    assert!(is_local_id(&id));
    let identity = ObligationIdentity {
        key,
        package: "c".to_string(),
        function_source_sha256: None,
        expanded_function_identity: None,
    };
    assert_eq!(identity.def_path(), "c::f::{closure#0}");
}

#[test]
fn the_function_source_digest_reads_tokens() {
    let a = function_source_digest("fn f() { a / b }");
    assert_eq!(a, function_source_digest("fn f()\n{\n    a / b\n}\n"));
    // rustfmt's respacing and reflow, and a comment, are not edits.
    assert_eq!(a, function_source_digest("fn f() { a/b }"));
    assert_eq!(a, function_source_digest("fn f() {\n    // why\n    a /* really */ / b\n}"));
    let call = function_source_digest("fn g() { foo(a,b) }");
    assert_eq!(call, function_source_digest("fn g() {\n    foo(\n        a,\n        b\n    )\n}"));
    assert_ne!(a, function_source_digest("fn f() { a / c }"));
    // A literal's content is code.
    assert_ne!(
        function_source_digest(r#"fn h() { p("a b") }"#),
        function_source_digest(r#"fn h() { p("a  b") }"#)
    );
    assert!(is_function_source_digest(&a));
}

#[test]
fn the_domain_is_pinned() {
    // A change to the encoding changes every committed baseline: bump the
    // domain's version with it.
    assert_eq!(OBLIGATION_ID_DOMAIN, b"trust-obligation-id/v2\0");
    assert_eq!(local_id("divzero", "stmt:0000000000000000", 0).len(), LOCAL_ID_HEX_LEN);
}
