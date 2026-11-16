//! One native API exercise used by both synthetic and real-DSO clients.
use super::pm;
use pm::Spacing;
use std::str::FromStr;

pub(crate) fn all_methods(input: pm::TokenStream) -> pm::TokenStream {
    assert_eq!(pm::tracked::env_var("B1_INJECTED").unwrap(), "compiler-owned");
    pm::tracked::path("worker-native-path");
    let span = pm::Span::call_site();
    assert!(!format!("{span:?}").is_empty());
    let _ = span.parent();
    assert!(span.eq(&span.source()));
    assert!(span.eq(&span.resolved_at(span)));
    assert!(!span.eq(&pm::Span::mixed_site()));
    let _ = span.byte_range();
    let _ = span.start();
    let _ = span.end();
    assert!(span.line() > 0);
    assert!(span.column() > 0);
    assert!(!span.file().is_empty());
    let _ = span.local_file();
    assert!(span.join(span).is_some());
    let _ = span.resolved_at(pm::Span::mixed_site());
    assert_eq!(span.source_text().as_deref(), Some("alpha"));
    let _ = span.save_span();
    let _ = pm::Span::recover_proc_macro_span(0);
    span.warning("worker native warning fixture").emit();
    let literal = pm::Literal::from_str("12u32").unwrap();
    assert!(literal.span().eq(&span));
    assert!(input.clone().into_iter().next().unwrap().span().eq(&span));
    assert!(literal.subspan(0..1).is_some());
    assert!(pm::Literal::from_str("not a literal").is_err());
    assert_eq!(pm::Ident::new("e\u{301}", span).to_string(), "é");
    let mut stream = pm::TokenStream::from(pm::TokenTree::Ident(pm::Ident::new_raw("type", span)));
    let group = pm::Group::new(pm::Delimiter::Brace, pm::TokenStream::from_str("nested").unwrap());
    let punct = pm::Punct::new('+', Spacing::Joint);
    stream.extend([
        pm::TokenTree::Group(group),
        pm::TokenTree::Punct(punct),
        pm::TokenTree::Literal(literal),
    ]);
    stream.extend([input.clone(), input.clone()]);
    assert!(!stream.is_empty());
    assert!(stream.to_string().contains("r#type"));
    let _trees: Vec<_> = stream.clone().into_iter().collect();
    let number = pm::TokenStream::from_str("42").unwrap();
    assert_eq!(number.expand_expr().unwrap().to_string(), "42");
    assert!(input.expand_expr().is_err());
    drop(stream);
    input
}

