extern crate proc_macro;

use proc_macro::{Group, Ident, Span, TokenStream, TokenTree};

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
                TokenTree::Group(group) => TokenTree::Group(Group::new(
                    group.delimiter(),
                    collapse_to_call_site(group.stream()),
                )),
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

/// A macro-emitted local with the same call-site identity as an outer
/// parameter is an actual lexical shadow. Native clauses must not recover the
/// hidden parameter merely because the verifier spelling erases that shadow.
#[proc_macro]
pub fn emit_collapsed_native_shadow(_input: TokenStream) -> TokenStream {
    collapse_to_call_site(
        "pub fn collapsed_native_shadow(mut n: u32, bound: u32) { let bound = 1u32; while n > 0 invariant bound > 0 decreases n { n -= 1; let _ = bound; } }"
            .parse()
            .expect("native-shadow fixture must tokenize"),
    )
}

fn rewrite_mixed_bound(stream: TokenStream) -> TokenStream {
    stream
        .into_iter()
        .map(|tree| match tree {
            TokenTree::Ident(ident) if ident.to_string() == "__mixed_bound" => {
                TokenTree::Ident(Ident::new("bound", Span::mixed_site()))
            }
            TokenTree::Group(group) => {
                let mut tree = TokenTree::Group(Group::new(
                    group.delimiter(),
                    rewrite_mixed_bound(group.stream()),
                ));
                tree.set_span(Span::call_site());
                tree
            }
            mut tree => {
                tree.set_span(Span::call_site());
                tree
            }
        })
        .collect()
}

/// Rust hygiene can keep a mixed-site local distinct from a call-site
/// parameter even though both render as `bound`. The verifier language has no
/// syntax-context spelling, so accepting either binding would be ambiguous.
#[proc_macro]
pub fn emit_distinct_native_collision(_input: TokenStream) -> TokenStream {
    rewrite_mixed_bound(
        "pub fn distinct_native_collision(mut n: u32, bound: u32) { let __mixed_bound = 1u32; while n > 0 invariant bound > 0 decreases n { n -= 1; let _ = __mixed_bound; } let _ = bound; }"
            .parse()
            .expect("hygienically distinct collision fixture must tokenize"),
    )
}

/// Function-level proposition and monitor maps are text-keyed too. Two
/// hygienically distinct parameters may therefore not share one displayed
/// spelling even when a clause token resolves to the call-site parameter.
#[proc_macro]
pub fn emit_distinct_native_parameters(_input: TokenStream) -> TokenStream {
    rewrite_mixed_bound(
        "pub fn distinct_native_parameters(bound: u32, __mixed_bound: u32) requires bound == bound { let _ = bound; let _ = __mixed_bound; }"
            .parse()
            .expect("hygienically distinct parameter fixture must tokenize"),
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
