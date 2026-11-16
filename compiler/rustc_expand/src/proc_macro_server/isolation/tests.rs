//! Trust (D21): real compiler token/handle round trips and hostile-input refusals.

use std::time::{Duration, Instant};

use rustc_parse::source_str_to_stream;
use rustc_span::{DUMMY_SP, FileName, create_default_session_globals_then, kw};
use trust_process_isolation::Limits;

use super::*;

fn adapter(invocation: u64) -> TokenAdapter {
    let limits = Limits {
        frame_bytes: 1 << 20,
        wire_bytes: 1 << 24,
        allocation_bytes: 1 << 28,
        values: 1 << 20,
        work: 1 << 24,
        calls: 1024,
        live_handles: 4096,
        depth: 32,
    };
    TokenAdapter::new(
        invocation,
        Budget::new(limits, Instant::now() + Duration::from_secs(30)).unwrap(),
    )
    .unwrap()
}

fn parse(psess: &ParseSess, source: &str) -> TokenStream {
    source_str_to_stream(psess, FileName::Custom("adapter.rs".into()), source.into(), None).unwrap()
}

// Compare the native proc-macro view, not raw internal tokens: the native
// bridge itself splits operators and normalizes invisible groups/comments.
fn native_view(stream: TokenStream) -> Vec<String> {
    Vec::<NativeTree>::from_internal(stream)
        .into_iter()
        .map(|tree| match tree {
            TokenTree::Group(Group { delimiter, stream, span }) => {
                let delimiter = match delimiter {
                    Delimiter::Parenthesis => 0,
                    Delimiter::Brace => 1,
                    Delimiter::Bracket => 2,
                    Delimiter::None => 3,
                };
                format!(
                    "group {delimiter} {:?} {:?} {:?} {:?}",
                    span.open,
                    span.close,
                    span.entire,
                    native_view(stream.unwrap_or_default())
                )
            }
            TokenTree::Punct(Punct { ch, joint, span }) => format!("punct {ch} {joint} {span:?}"),
            TokenTree::Ident(Ident { sym, kind, span }) => {
                format!("ident {:?} {:?} {span:?}", sym.as_str(), kind.prefix())
            }
            TokenTree::Literal(Literal { kind, symbol, suffix, span }) => format!(
                "literal {kind:?} {:?} {:?} {span:?}",
                symbol.as_str(),
                suffix.map(|s| s.as_str().to_owned())
            ),
        })
        .collect()
}

#[test]
fn parsed_compiler_tokens_round_trip_through_b1_handles() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        for source in [
            "struct Déjà<T> { r#type: T } impl<T> Déjà<T> { fn get<'a>(&'a self) -> &'a T { &self.r#type } }",
            "a <= b && c >>= 2; 'life; [] {} ()",
            r###"b'x' 'λ' 12u64 1.25f32 "text\n" r##"raw"## b"bytes" br#"raw bytes"# c"cstr" cr#"raw c"#"###,
            "/// expanded documentation\nstruct Item;",
        ] {
            let original = parse(&psess, source);
            let expected = native_view(original.clone());
            let mut owner = adapter(1);
            let handle = owner.store_stream(original).unwrap();
            let wire = owner.export_stream(handle).unwrap();
            let binding = trust_process_isolation::Binding {
                version: trust_process_isolation::PROTOCOL_VERSION,
                invocation: 1,
                compiler: [1; 32],
                worker: [2; 32],
                artifact: [3; 32],
                metadata: [4; 32],
                unit: [5; 32],
                input_closure: [6; 32],
                host_abi: [7; 32],
            };
            let envelope = trust_process_isolation::Envelope {
                binding,
                message: trust_process_isolation::Message::Reply {
                    id: 1,
                    value: trust_process_isolation::Value::Trees(wire),
                },
            };
            let encoded = trust_process_isolation::encode(&envelope, &owner.budget).unwrap();
            let decoded = trust_process_isolation::decode(&encoded, &owner.budget).unwrap();
            let trust_process_isolation::Message::Reply {
                value: trust_process_isolation::Value::Trees(wire),
                ..
            } = decoded.message
            else {
                panic!("wrong decoded value")
            };
            let result = owner.import_trees(&psess, &wire).unwrap();
            assert_eq!(native_view(result), expected, "{source}");
        }
    });
}

#[test]
fn identifiers_follow_native_normalization_and_raw_rules() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        for (text, raw, expected) in [
            ("$crate", false, "$crate"),
            ("_", false, "_"),
            ("e\u{301}", false, "é"),
            ("type", true, "type"),
        ] {
            let mut owner = adapter(1);
            let span = owner.store_span(DUMMY_SP).unwrap();
            let result = owner
                .import_trees(&psess, &[Tree::Ident { symbol: text.into(), is_raw: raw, span }])
                .unwrap();
            let tokens = Vec::<NativeTree>::from_internal(result);
            let TokenTree::Ident(ident) = &tokens[0] else { panic!("identifier lost") };
            assert_eq!(ident.sym.as_str(), expected);
            assert!(ident.kind == if raw { IdentKind::Raw } else { IdentKind::Normal });
        }
    });
}

#[test]
fn native_integral_float_and_negative_numeric_literals_keep_their_kind() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        for (kind, symbol, suffix) in [
            (3, "1", Some("f64")),
            (3, "-1", Some("f32")),
            (2, "-17", Some("i32")),
            (3, "-1.25", None),
        ] {
            let mut owner = adapter(1);
            let span = owner.store_span(DUMMY_SP).unwrap();
            let result = owner
                .import_trees(
                    &psess,
                    &[Tree::Literal(trust_process_isolation::Literal {
                        kind,
                        raw_hashes: 0,
                        symbol: symbol.into(),
                        suffix: suffix.map(str::to_owned),
                        span,
                    })],
                )
                .unwrap();
            let expected_kind = if kind == 3 { tk::Float } else { tk::Integer };
            let expected = TokenStream::new(
                token_tree_to_internal(
                    TokenTree::Literal(Literal {
                        kind: if kind == 3 { LitKind::Float } else { LitKind::Integer },
                        symbol: Symbol::intern(symbol),
                        suffix: suffix.map(Symbol::intern),
                        span: DUMMY_SP,
                    }),
                    &psess,
                )
                .into_vec(),
            );
            assert_eq!(native_view(result.clone()), native_view(expected));
            assert!(result.iter().any(|tree| matches!(tree,
                tokenstream::TokenTree::Token(tk::Token { kind: tk::Literal(lit), .. }, _) if lit.kind == expected_kind)));
        }
    });
}

#[test]
fn group_spans_and_punctuation_jointness_use_compiler_owned_values() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        let parsed = parse(&psess, "(a)");
        let tokenstream::TokenTree::Delimited(spans, _, _, _) = parsed.get(0).unwrap() else {
            panic!()
        };
        let mut owner = adapter(1);
        let open = owner.store_span(spans.open).unwrap();
        let close = owner.store_span(spans.close).unwrap();
        let entire = owner.store_span(spans.entire()).unwrap();
        let inner = owner.store_stream(parse(&psess, "a")).unwrap();
        let trees = [
            Tree::Group { delimiter: 0, stream: Some(inner), spans: [open, close, entire] },
            Tree::Punct { ch: b'=', joint: true, span: open },
        ];
        let result = owner.import_trees(&psess, &trees).unwrap();
        let native = Vec::<NativeTree>::from_internal(result);
        let TokenTree::Group(group) = &native[0] else { panic!() };
        assert_eq!(group.span.open, spans.open);
        assert_eq!(group.span.close, spans.close);
        assert_eq!(group.span.entire, spans.entire());
        assert!(matches!(&native[1], TokenTree::Punct(Punct { ch: b'=', joint: true, .. })));
    });
}

#[test]
fn malformed_tokens_fail_explicitly_and_poison_the_original_grant() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        for invalid in 0..8 {
            let mut owner = adapter(1);
            let span = owner.store_span(DUMMY_SP).unwrap();
            let tree = match invalid {
                0 => Tree::Punct { ch: 0, joint: false, span },
                1 => Tree::Ident { symbol: "1bad".into(), is_raw: false, span },
                2 => Tree::Ident { symbol: "crate".into(), is_raw: true, span },
                3 => Tree::Group { delimiter: 4, stream: None, spans: [span; 3] },
                n => Tree::Literal(trust_process_isolation::Literal {
                    kind: if n == 4 { 10 } else { 2 },
                    raw_hashes: if n == 5 { 1 } else { 0 },
                    symbol: match n {
                        6 => "12 34".into(),
                        7 => "(".repeat(10_000),
                        _ => "12".into(),
                    },
                    suffix: None,
                    span,
                }),
            };
            let error = owner.import_trees(&psess, &[tree]).unwrap_err();
            assert!(matches!(error, Error::InvalidWire(_)), "{error:?}");
            assert_eq!(owner.budget.check(), Err(error.clone()));
            assert_eq!(owner.values.live(), 0);
            assert_eq!(owner.store_span(DUMMY_SP), Err(error));
        }
    });
}

#[test]
fn foreign_stale_and_duplicate_consuming_handles_are_errors() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        for invalid in 0..4 {
            let mut owner = adapter(1);
            let mut foreign = adapter(2);
            let mut span = owner.store_span(DUMMY_SP).unwrap();
            if invalid == 0 {
                span = foreign.store_span(DUMMY_SP).unwrap();
            }
            if invalid == 1 {
                span.generation += 1;
            }
            let inner = owner.store_stream(parse(&psess, "a")).unwrap();
            if invalid == 3 {
                span = inner;
            }
            let tree = Tree::Group { delimiter: 0, stream: Some(inner), spans: [span; 3] };
            let trees = if invalid == 2 { vec![tree.clone(), tree] } else { vec![tree] };
            assert!(matches!(owner.import_trees(&psess, &trees), Err(Error::Handle(_))));
            assert_eq!(owner.values.live(), 0);
        }
        let mut owner = adapter(1);
        let span = owner.store_span(DUMMY_SP).unwrap();
        let inner = owner.store_stream(parse(&psess, "a")).unwrap();
        let tree = Tree::Group { delimiter: 0, stream: Some(inner), spans: [span; 3] };
        owner.import_trees(&psess, &[tree.clone()]).unwrap();
        assert_eq!(owner.import_trees(&psess, &[tree]).unwrap_err(), Error::Handle("consumed"));
    });
}

#[test]
fn quoted_span_lookup_is_checked_and_keeps_compiler_context() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        let tokens = parse(&psess, "name");
        let source = tokens.get(0).unwrap().span();
        let spans = [source];
        let mut owner = adapter(1);
        let handle = owner.recover_quoted_span(0, DUMMY_SP, |i| spans.get(i).copied()).unwrap();
        assert_eq!(owner.span(handle).unwrap(), source.with_ctxt(DUMMY_SP.ctxt()));
        assert_eq!(
            owner.recover_quoted_span(u64::MAX, DUMMY_SP, |i| spans.get(i).copied()),
            Err(Error::InvalidWire("quoted span index"))
        );
        assert_eq!(owner.values.live(), 0);
    });
}

#[test]
fn unsupported_native_tokens_and_exhausted_budgets_refuse() {
    create_default_session_globals_then(|| {
        let forced =
            TokenStream::token_alone(tk::Ident(kw::Async, tk::IdentKind::ForcedKeyword), DUMMY_SP);
        assert!(matches!(adapter(1).store_stream(forced), Err(Error::InvalidWire(_))));
        let boolean = TokenStream::token_alone(
            tk::TokenKind::Literal(tk::Lit::new(tk::Bool, kw::True, None)),
            DUMMY_SP,
        );
        assert!(matches!(adapter(1).store_stream(boolean), Err(Error::InvalidWire(_))));
        assert_eq!(
            literal_kind(LitKind::ErrWithGuar),
            Err(Error::InvalidWire("error-guaranteed literal"))
        );
        let psess = ParseSess::new();
        let mut owner = adapter(1);
        let mut limits = owner.budget.limits();
        limits.allocation_bytes = 1;
        let small = Budget::new(limits, owner.budget.deadline()).unwrap();
        assert!(matches!(TokenAdapter::new(1, small), Err(Error::Budget(_))));
        limits = owner.budget.limits();
        limits.work = 1;
        owner =
            TokenAdapter::new(1, Budget::new(limits, owner.budget.deadline()).unwrap()).unwrap();
        assert!(matches!(owner.store_stream(parse(&psess, "name other")), Err(Error::Budget(_))));
    });
}

#[test]
fn wrapping_a_valid_stream_cannot_exceed_the_original_depth_grant() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        let mut limits = adapter(1).budget.limits();
        limits.depth = 2;
        let budget = Budget::new(limits, Instant::now() + Duration::from_secs(30)).unwrap();
        let mut owner = TokenAdapter::new(1, budget).unwrap();
        let inner = owner.store_stream(parse(&psess, "(())")).unwrap();
        let span = owner.store_span(DUMMY_SP).unwrap();
        let wrapper = Tree::Group { delimiter: 0, stream: Some(inner), spans: [span; 3] };
        assert_eq!(owner.import_trees(&psess, &[wrapper]).unwrap_err(), Error::Budget("depth"));
        assert_eq!(owner.values.live(), 0);
    });
}

#[test]
fn equal_native_spans_reuse_only_live_canonical_handles() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        let tokens = parse(&psess, "alpha beta");
        let first = tokens.get(0).unwrap().span();
        let second = tokens.get(1).unwrap().span();
        let mut owner = adapter(1);
        let a = owner.store_span(first).unwrap();
        let usage = owner.budget.usage().unwrap();
        let repeated = owner.store_span(first).unwrap();
        assert_eq!(a, repeated);
        assert_eq!(owner.values.live(), 1);
        assert!(owner.budget.usage().unwrap().work > usage.work);
        assert_eq!(owner.budget.usage().unwrap().allocation_bytes, usage.allocation_bytes);
        let b = owner.store_span(second).unwrap();
        assert_ne!(a, b);
        assert_ne!(first, second);
        owner.clear();
        assert_eq!(owner.store_span(first), Err(Error::Phase));
        assert_eq!(owner.values.live(), 0);
        assert_eq!(owner.budget.check(), Err(Error::Phase));
    });
}

#[test]
fn every_exported_span_and_quoted_recovery_uses_canonical_identity() {
    create_default_session_globals_then(|| {
        let psess = ParseSess::new();
        let tokens = parse(&psess, "seed");
        let span = tokens.get(0).unwrap().span();
        let mut owner = adapter(1);
        let expected = owner.store_span(span).unwrap();
        let TokenTree::Ident(ident) = Vec::<NativeTree>::from_internal(tokens).remove(0) else {
            panic!("identifier fixture");
        };
        let literal = parse_literal(&psess, "1", span).unwrap();
        let native = [
            TokenTree::Group(Group {
                delimiter: Delimiter::Brace,
                stream: None,
                span: DelimSpan::from_single(span),
            }),
            TokenTree::Punct(Punct { ch: b'+', joint: false, span }),
            TokenTree::Ident(ident),
            TokenTree::Literal(literal),
        ];
        for tree in native {
            for _ in 0..2 {
                match owner.export_tree(tree.clone()).unwrap() {
                    Tree::Group { spans, .. } => assert_eq!(spans, [expected; 3]),
                    Tree::Punct { span, .. } | Tree::Ident { span, .. } => {
                        assert_eq!(span, expected)
                    }
                    Tree::Literal(l) => assert_eq!(l.span, expected),
                }
            }
        }
        assert_eq!(owner.recover_quoted_span(0, span, |_| Some(span)).unwrap(), expected);
        assert_eq!(owner.values.live(), 1);
    });
}
