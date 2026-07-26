extern crate proc_macro;

use proc_macro::{Group, Span, TokenStream, TokenTree};

fn signature(stream: TokenStream) -> Vec<String> {
    stream
        .into_iter()
        .map(|tree| match tree {
            TokenTree::Ident(ident) => format!("ident:{ident}"),
            TokenTree::Punct(punct) => {
                format!("punct:{}:{:?}", punct.as_char(), punct.spacing())
            }
            TokenTree::Literal(literal) => format!("literal:{literal}"),
            TokenTree::Group(group) => format!("group:{:?}:{}", group.delimiter(), group.stream()),
        })
        .collect()
}

#[proc_macro]
pub fn assert_trust_prime_boundary(input: TokenStream) -> TokenStream {
    let actual = signature(input.clone());
    let actual_refs: Vec<&str> = actual.iter().map(String::as_str).collect();
    assert!(
        matches!(
            actual_refs.as_slice(),
            ["punct:':Joint", "ident:__trust_prime"]
                | ["ident:x", "punct:':Alone"]
                | ["ident:x", "punct:':Joint", "punct:':Alone"]
                | ["ident:r#type", "punct:':Alone"]
        ),
        "prime/lifetime token identity changed: {actual:?}"
    );

    let rendered = input.to_string();
    let reparsed: TokenStream = rendered.parse().expect("rendered token stream must reparse");
    assert_eq!(signature(reparsed), actual, "token-stream round-trip changed identity");

    TokenStream::new()
}

fn collapse_to_call_site(stream: TokenStream) -> TokenStream {
    stream
        .into_iter()
        .map(|tree| {
            let mut tree = match tree {
                TokenTree::Group(group) => {
                    TokenTree::Group(Group::new(
                        group.delimiter(),
                        collapse_to_call_site(group.stream()),
                    ))
                }
                tree => tree,
            };
            tree.set_span(Span::call_site());
            tree
        })
        .collect()
}

/// Native-clause parsing must advance by token identity/count, not by source
/// span: proc macros are allowed to give every emitted token the same span.
#[proc_macro]
pub fn emit_collapsed_native_contract(_input: TokenStream) -> TokenStream {
    collapse_to_call_site(
        "pub fn collapsed_native_contract(mut n: u32, by: u32) requires by == by ensures result == () { while n > 0 decreases n invariant n <= 1 { n -= 1; } }"
            .parse()
            .expect("native-contract fixture must tokenize"),
    )
}

/// Stateful Clean islands cannot be ordered by source position when a proc
/// macro deliberately assigns every emitted token the same call-site span.
/// The compiler must diagnose the ambiguity instead of inventing DefId order.
#[proc_macro]
pub fn emit_collapsed_clean_islands(_input: TokenStream) -> TokenStream {
    collapse_to_call_site(
        "clean { theorem first : 0 = 0 := rfl } clean { theorem second : 0 = 0 := first }"
            .parse()
            .expect("Clean-island fixture must tokenize"),
    )
}
