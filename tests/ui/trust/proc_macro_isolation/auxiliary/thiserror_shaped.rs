//! A derive with the shape of `thiserror`: a format string per enum variant,
//! positional and named fields, and a `#[from]` conversion. `proc_macro` alone.
extern crate proc_macro;

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

enum Fields {
    Unit,
    Tuple(usize),
    Named(Vec<Ident>),
}

struct Variant {
    name: Ident,
    message: Literal,
    fields: Fields,
    /// The type of a single `#[from]` field.
    from: Option<TokenStream>,
}

fn error(span: Span, message: &str) -> TokenStream {
    let text = format!("compile_error!({message:?});");
    let mut tokens: Vec<TokenTree> = text.parse::<TokenStream>().unwrap().into_iter().collect();
    for token in &mut tokens {
        token.set_span(span);
    }
    tokens.into_iter().collect()
}

/// Split a group's stream at top-level commas, angle brackets respected.
fn split(stream: TokenStream) -> Vec<Vec<TokenTree>> {
    let mut parts = vec![Vec::new()];
    let mut depth = 0_i32;
    for token in stream {
        match &token {
            TokenTree::Punct(p) if p.as_char() == '<' => depth += 1,
            TokenTree::Punct(p) if p.as_char() == '>' => depth -= 1,
            TokenTree::Punct(p) if p.as_char() == ',' && depth == 0 => {
                parts.push(Vec::new());
                continue;
            }
            _ => {}
        }
        parts.last_mut().unwrap().push(token);
    }
    parts.retain(|part| !part.is_empty());
    parts
}

fn is_attribute(tokens: &[TokenTree], name: &str) -> Option<Group> {
    match tokens {
        [TokenTree::Punct(hash), TokenTree::Group(attribute), ..] if hash.as_char() == '#' => {
            let mut inner = attribute.stream().into_iter();
            match inner.next() {
                Some(TokenTree::Ident(word)) if word.to_string() == name => Some(match inner.next()
                {
                    Some(TokenTree::Group(arguments)) => arguments,
                    _ => Group::new(Delimiter::Parenthesis, TokenStream::new()),
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

fn variant(tokens: Vec<TokenTree>) -> Result<Variant, TokenStream> {
    let mut rest = &tokens[..];
    let mut message = None;
    while let [TokenTree::Punct(hash), TokenTree::Group(_), tail @ ..] = rest {
        if hash.as_char() != '#' {
            break;
        }
        if let Some(arguments) = is_attribute(rest, "error") {
            match arguments.stream().into_iter().next() {
                Some(TokenTree::Literal(literal)) => message = Some(literal),
                _ => return Err(error(arguments.span(), "expected `#[error(\"…\")]`")),
            }
        }
        rest = tail;
    }
    let [TokenTree::Ident(name), rest @ ..] = rest else {
        return Err(error(Span::call_site(), "expected a variant name"));
    };
    let Some(message) = message else {
        return Err(error(name.span(), "missing `#[error(\"…\")]`"));
    };
    let mut from = None;
    let fields = match rest {
        [] => Fields::Unit,
        [TokenTree::Group(group)] if group.delimiter() == Delimiter::Parenthesis => {
            let parts = split(group.stream());
            if let [only] = &parts[..] {
                if is_attribute(only, "from").is_some() {
                    from = Some(only[2..].iter().cloned().collect());
                }
            }
            Fields::Tuple(parts.len())
        }
        [TokenTree::Group(group)] if group.delimiter() == Delimiter::Brace => Fields::Named(
            split(group.stream())
                .into_iter()
                .filter_map(|part| match part.first() {
                    Some(TokenTree::Ident(field)) => Some(field.clone()),
                    _ => None,
                })
                .collect(),
        ),
        [other, ..] => return Err(error(other.span(), "unsupported variant")),
    };
    Ok(Variant { name: name.clone(), message, fields, from })
}

#[proc_macro_derive(Failure, attributes(error, from))]
pub fn derive_failure(input: TokenStream) -> TokenStream {
    let mut tokens = input.into_iter();
    let name = loop {
        match tokens.next() {
            Some(TokenTree::Ident(word)) if word.to_string() == "enum" => match tokens.next() {
                Some(TokenTree::Ident(name)) => break name,
                _ => return error(word.span(), "expected an enum name"),
            },
            Some(_) => {}
            None => return error(Span::call_site(), "`Failure` is derived for enums only"),
        }
    };
    let Some(TokenTree::Group(body)) = tokens.next() else {
        return error(name.span(), "expected variants");
    };
    let mut variants = Vec::new();
    for part in split(body.stream()) {
        match variant(part) {
            Ok(variant) => variants.push(variant),
            Err(error) => return error,
        }
    }

    let mut arms = TokenStream::new();
    let mut conversions = TokenStream::new();
    for variant in &variants {
        // `Self::Name(_0, _1) => write!(f, "…", _0, _1),`
        let (pattern, arguments): (TokenStream, String) = match &variant.fields {
            Fields::Unit => (TokenStream::new(), String::new()),
            Fields::Tuple(count) => {
                let names: Vec<String> = (0..*count).map(|index| format!("_{index}")).collect();
                let pattern = names.join(", ").parse::<TokenStream>().unwrap();
                (
                    TokenTree::Group(Group::new(Delimiter::Parenthesis, pattern)).into(),
                    names.iter().map(|name| format!(", {name}")).collect(),
                )
            }
            Fields::Named(fields) => {
                // Named fields are captured by the format string itself, so the
                // bindings keep the spans the user wrote them with.
                let mut pattern = TokenStream::new();
                for field in fields {
                    pattern.extend([
                        TokenTree::Ident(field.clone()),
                        Punct::new(',', Spacing::Alone).into(),
                    ]);
                }
                (TokenTree::Group(Group::new(Delimiter::Brace, pattern)).into(), String::new())
            }
        };
        arms.extend(format!("Self::{}", variant.name).parse::<TokenStream>().unwrap());
        arms.extend(pattern);
        arms.extend("=> ::core::write!".parse::<TokenStream>().unwrap());
        let mut call = TokenStream::new();
        call.extend([
            TokenTree::Ident(Ident::new("formatter", Span::mixed_site())),
            Punct::new(',', Spacing::Alone).into(),
            TokenTree::Literal(variant.message.clone()),
        ]);
        call.extend(arguments.parse::<TokenStream>().unwrap());
        arms.extend([
            TokenTree::Group(Group::new(Delimiter::Parenthesis, call)),
            Punct::new(',', Spacing::Alone).into(),
        ]);

        if let Some(source) = &variant.from {
            let mut conversion: TokenStream = "impl ::core::convert::From<".parse().unwrap();
            conversion.extend(source.clone());
            conversion.extend(format!("> for {name}").parse::<TokenStream>().unwrap());
            let mut function: TokenStream = "fn from".parse().unwrap();
            let mut parameters: TokenStream = "source:".parse().unwrap();
            parameters.extend(source.clone());
            function.extend([TokenTree::Group(Group::new(Delimiter::Parenthesis, parameters))]);
            function.extend(
                format!("-> Self {{ {name}::{}(source) }}", variant.name)
                    .parse::<TokenStream>()
                    .unwrap(),
            );
            conversion.extend([TokenTree::Group(Group::new(Delimiter::Brace, function))]);
            conversions.extend(conversion);
        }
    }

    let mut display: TokenStream = format!("impl ::core::fmt::Display for {name}").parse().unwrap();
    let mut function: TokenStream = "fn fmt".parse().unwrap();
    let mut parameters: TokenStream = "&self,".parse().unwrap();
    parameters.extend([
        TokenTree::Ident(Ident::new("formatter", Span::mixed_site())),
        Punct::new(':', Spacing::Alone).into(),
    ]);
    parameters.extend("&mut ::core::fmt::Formatter<'_>".parse::<TokenStream>().unwrap());
    function.extend([TokenTree::Group(Group::new(Delimiter::Parenthesis, parameters))]);
    function.extend("-> ::core::fmt::Result".parse::<TokenStream>().unwrap());
    let mut matched: TokenStream = "match self".parse().unwrap();
    matched.extend([TokenTree::Group(Group::new(Delimiter::Brace, arms))]);
    function.extend([TokenTree::Group(Group::new(Delimiter::Brace, matched))]);
    display.extend([TokenTree::Group(Group::new(Delimiter::Brace, function))]);

    let mut output = display;
    output.extend(
        format!("impl ::std::error::Error for {name} {{}}").parse::<TokenStream>().unwrap(),
    );
    output.extend(conversions);
    output
}
