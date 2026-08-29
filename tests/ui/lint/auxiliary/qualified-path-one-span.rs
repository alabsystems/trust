// Emits a qualified path whose segments ALL carry a single span taken from the
// CALLER'S OWN SOURCE — the shape serde_derive produces for
// `#[serde(with = "crate::a::b")]`, where the path is rebuilt from a string
// literal and every segment inherits that literal's real-source span.
//
// Taking the span from the macro's INPUT is load-bearing. `Span::call_site()`
// would be an EXPANSION span, and `lint_unused_qualifications` bails early on
// `from_expansion()`, so a call_site-spanned path never reaches the code under
// test — a version of this aux crate that used it produced a test which passed
// with the fix reverted, i.e. proved nothing.

extern crate proc_macro;

use proc_macro::{Delimiter, Group, Ident, Punct, Spacing, TokenStream, TokenTree};

#[proc_macro]
pub fn call_via_one_span_path(input: TokenStream) -> TokenStream {
    // Borrow the span of the caller's own token: real source, not an expansion.
    let anchor = input
        .into_iter()
        .next()
        .expect("pass one ident to anchor the span");
    let sp = anchor.span();

    let seg = |name: &str| TokenTree::Ident(Ident::new(name, sp));
    let mut c1 = Punct::new(':', Spacing::Joint);
    c1.set_span(sp);
    let mut c2 = Punct::new(':', Spacing::Alone);
    c2.set_span(sp);
    let mut args = Group::new(Delimiter::Parenthesis, TokenStream::new());
    args.set_span(sp);

    let mut out = TokenStream::new();
    out.extend([
        seg("inner"),
        TokenTree::Punct(c1),
        TokenTree::Punct(c2),
        seg("helper"),
        TokenTree::Group(args),
    ]);
    out
}
