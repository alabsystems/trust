use trust_process_isolation::{Method, Type};

// Test-only source guard, deliberately independent of wire encode/decode. No
// compiler library or private documentation is embedded into the crate.
#[test]
fn native_api_names_types_arity_and_ownership_match() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
    let source =
        std::fs::read_to_string(root.join("library/proc_macro/src/bridge/mod.rs")).unwrap();
    let body = source
        .split("macro_rules! with_api {")
        .nth(1)
        .unwrap()
        .split("pub(crate) struct Methods;")
        .next()
        .unwrap();
    let mut entries = Vec::new();
    for declaration in body.split("fn ").skip(1) {
        let (name, rest) = declaration.split_once('(').unwrap();
        let mut depth = 1usize;
        let mut closing = None;
        for (i, ch) in rest.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        closing = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }
        let closing = closing.unwrap();
        let args = &rest[..closing];
        let tail = rest[closing + 1..].split(';').next().unwrap();
        let mut parts = Vec::new();
        let mut start = 0;
        let mut nesting = 0usize;
        for (i, ch) in args.char_indices() {
            match ch {
                '<' | '(' | '[' => nesting += 1,
                '>' | ')' | ']' => nesting -= 1,
                ',' if nesting == 0 => {
                    if !args[start..i].trim().is_empty() {
                        parts.push(&args[start..i]);
                    }
                    start = i + 1;
                }
                _ => {}
            }
        }
        if !args[start..].trim().is_empty() {
            parts.push(&args[start..]);
        }
        let types: Vec<_> = parts
            .iter()
            .map(|p| {
                p.split_once(':')
                    .unwrap()
                    .1
                    .chars()
                    .filter(|c| !c.is_whitespace())
                    .collect::<String>()
            })
            .collect();
        let result = tail
            .trim()
            .strip_prefix("->")
            .unwrap_or("()")
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect::<String>();
        entries.push((name.trim().to_string(), types, result));
    }
    assert_eq!(entries.len(), Method::ALL.len());
    for ((name, args, result), method) in entries.iter().zip(Method::ALL) {
        assert_eq!(name, method.name());
        assert_eq!(args.len(), method.arguments().len(), "{name}");
        for (index, (arg, expected)) in args.iter().zip(method.arguments()).enumerate() {
            assert_eq!(translate(arg), *expected, "{name} arg {index}");
            let consumes = arg.contains("$TokenStream") && !arg.starts_with('&');
            assert_eq!(consumes, method.consumes(index), "{name} ownership {index}");
        }
        assert_eq!(translate(result), method.response(), "{name} result");
    }
}

fn translate(native: &str) -> Type {
    match native {
        "()" => Type::Unit,
        "bool" => Type::Bool,
        "usize" => Type::U64,
        "String" | "&str" | "$Symbol" => Type::Text,
        "Option<String>" | "Option<&str>" => Type::OptionalText,
        "$TokenStream" | "&$TokenStream" => Type::Stream,
        "$Span" => Type::Span,
        "Option<$TokenStream>" => Type::OptionalStream,
        "Option<$Span>" => Type::OptionalSpan,
        "TokenTree<$TokenStream,$Span,$Symbol>" => Type::Tree,
        "Vec<TokenTree<$TokenStream,$Span,$Symbol>>" => Type::Trees,
        "Vec<$TokenStream>" => Type::Streams,
        "Bound<usize>" => Type::Bound,
        "Range<usize>" => Type::Range,
        "Literal<$Span,$Symbol>" => Type::Literal,
        "Diagnostic<$Span>" => Type::Diagnostic,
        "Result<Literal<$Span,$Symbol>,String>" => Type::LiteralOrText,
        "Result<$TokenStream,()>" => Type::StreamOrUnit,
        "Result<$TokenStream,String>" => Type::StreamOrText,
        "Result<$Symbol,()>" => Type::TextOrUnit,
        other => panic!("unmapped native bridge type {other}"),
    }
}
