//! A derive with the shape of `serde_derive`: helper attributes on fields, a
//! generic type, and an impl built partly from token trees and partly from
//! parsed source text. It uses `proc_macro` alone, as the suite has no `syn`.
extern crate proc_macro;

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

struct Field {
    name: Ident,
    rename: Option<Literal>,
    skip: bool,
}

fn error(span: Span, message: &str) -> TokenStream {
    let mut call = TokenStream::new();
    call.extend([TokenTree::Literal(Literal::string(message))]);
    let mut tokens: Vec<TokenTree> = vec![
        Ident::new("compile_error", span).into(),
        Punct::new('!', Spacing::Alone).into(),
        Group::new(Delimiter::Parenthesis, call).into(),
        Punct::new(';', Spacing::Alone).into(),
    ];
    for token in &mut tokens {
        token.set_span(span);
    }
    tokens.into_iter().collect()
}

/// `#[shape(rename = "…")]` and `#[shape(skip)]`.
fn helper(field: &mut Field, attribute: Group) -> Result<(), TokenStream> {
    let mut tokens = attribute.stream().into_iter();
    match tokens.next() {
        Some(TokenTree::Ident(name)) if name.to_string() == "shape" => {}
        _ => return Ok(()),
    }
    let Some(TokenTree::Group(arguments)) = tokens.next() else {
        return Err(error(attribute.span(), "`shape` takes arguments"));
    };
    let mut arguments = arguments.stream().into_iter();
    match arguments.next() {
        Some(TokenTree::Ident(key)) if key.to_string() == "skip" => field.skip = true,
        Some(TokenTree::Ident(key)) if key.to_string() == "rename" => {
            match (arguments.next(), arguments.next()) {
                (Some(TokenTree::Punct(equals)), Some(TokenTree::Literal(value)))
                    if equals.as_char() == '=' =>
                {
                    field.rename = Some(value)
                }
                _ => return Err(error(key.span(), "expected `rename = \"name\"`")),
            }
        }
        Some(other) => return Err(error(other.span(), "unknown `shape` argument")),
        None => return Err(error(attribute.span(), "empty `shape` attribute")),
    }
    Ok(())
}

fn fields(body: Group) -> Result<Vec<Field>, TokenStream> {
    let mut result = Vec::new();
    let mut tokens = body.stream().into_iter().peekable();
    while tokens.peek().is_some() {
        let mut attributes = Vec::new();
        let name = loop {
            match tokens.next() {
                Some(TokenTree::Punct(hash)) if hash.as_char() == '#' => match tokens.next() {
                    Some(TokenTree::Group(attribute)) => attributes.push(attribute),
                    _ => return Err(error(hash.span(), "expected an attribute")),
                },
                Some(TokenTree::Ident(word)) if word.to_string() == "pub" => {
                    if let Some(TokenTree::Group(_)) = tokens.peek() {
                        tokens.next();
                    }
                }
                Some(TokenTree::Ident(name)) => break name,
                Some(other) => return Err(error(other.span(), "expected a field name")),
                None => return Err(error(body.span(), "expected a field name")),
            }
        };
        let mut field = Field { name, rename: None, skip: false };
        for attribute in attributes {
            helper(&mut field, attribute)?;
        }
        // The type runs to the next comma outside angle brackets.
        let mut depth = 0_i32;
        for token in tokens.by_ref() {
            match token {
                TokenTree::Punct(p) if p.as_char() == '<' => depth += 1,
                TokenTree::Punct(p) if p.as_char() == '>' => depth -= 1,
                TokenTree::Punct(p) if p.as_char() == ',' && depth == 0 => break,
                _ => {}
            }
        }
        result.push(field);
    }
    Ok(result)
}

#[proc_macro_derive(Shape, attributes(shape))]
pub fn derive_shape(input: TokenStream) -> TokenStream {
    let mut tokens = input.into_iter().peekable();
    // Outer attributes and visibility, then `struct Name`.
    let name = loop {
        match tokens.next() {
            Some(TokenTree::Ident(word)) if word.to_string() == "struct" => match tokens.next() {
                Some(TokenTree::Ident(name)) => break name,
                _ => return error(word.span(), "expected a struct name"),
            },
            Some(TokenTree::Ident(word)) if word.to_string() == "enum" => {
                return error(word.span(), "`Shape` is derived for structs only");
            }
            Some(_) => {}
            None => return error(Span::call_site(), "expected a struct"),
        }
    };
    // `<A, B>`: plain type parameters only.
    let mut parameters = Vec::new();
    if matches!(tokens.peek(), Some(TokenTree::Punct(p)) if p.as_char() == '<') {
        tokens.next();
        for token in tokens.by_ref() {
            match token {
                TokenTree::Punct(p) if p.as_char() == '>' => break,
                TokenTree::Punct(p) if p.as_char() == ',' => {}
                TokenTree::Ident(parameter) => parameters.push(parameter),
                other => return error(other.span(), "only plain type parameters are supported"),
            }
        }
    }
    let body = match tokens.next() {
        Some(TokenTree::Group(body)) if body.delimiter() == Delimiter::Brace => body,
        _ => return error(name.span(), "expected named fields"),
    };
    let fields = match fields(body) {
        Ok(fields) => fields,
        Err(error) => return error,
    };

    // The entries are built token by token, each literal carrying its field's span.
    let mut entries = TokenStream::new();
    for field in fields.iter().filter(|field| !field.skip) {
        let mut key = match &field.rename {
            Some(rename) => rename.clone(),
            None => Literal::string(&field.name.to_string()),
        };
        key.set_span(field.name.span());
        let value: TokenStream =
            format!("::std::format!(\"{{:?}}\", &self.{})", field.name).parse().unwrap();
        let mut entry = TokenStream::new();
        entry.extend([TokenTree::Literal(key), Punct::new(',', Spacing::Alone).into()]);
        entry.extend(value);
        entries.extend([
            TokenTree::Group(Group::new(Delimiter::Parenthesis, entry)),
            Punct::new(',', Spacing::Alone).into(),
        ]);
    }

    // The impl header and items come from source text.
    let bounded: Vec<String> =
        parameters.iter().map(|p| format!("{p}: ::core::fmt::Debug")).collect();
    let plain: Vec<String> = parameters.iter().map(|p| p.to_string()).collect();
    let header: TokenStream = format!(
        "impl<{}> Shape for {name}<{}>",
        bounded.join(", "),
        plain.join(", "),
    )
    .parse()
    .unwrap();
    let skipped = fields.iter().filter(|field| field.skip).count();
    let mut items: TokenStream = format!(
        "const NAME: &'static str = {:?}; const SKIPPED: usize = {skipped}usize; \
         fn fields(&self) -> ::std::vec::Vec<(&'static str, ::std::string::String)>",
        name.to_string(),
    )
    .parse()
    .unwrap();
    let mut vector: TokenStream = "::std::vec!".parse().unwrap();
    vector.extend([TokenTree::Group(Group::new(Delimiter::Bracket, entries))]);
    items.extend([TokenTree::Group(Group::new(Delimiter::Brace, vector))]);

    let mut output = header;
    output.extend([TokenTree::Group(Group::new(Delimiter::Brace, items))]);
    output
}
