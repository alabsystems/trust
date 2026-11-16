extern crate proc_macro;

use proc_macro::{Group, Span, TokenStream, TokenTree};

// Trust: recursively overwrite every token/group span with one actual call-site
// span. Distinct attributes thus cannot be distinguished by source locations.
fn same_span(tokens: TokenStream, span: Span) -> TokenStream {
    tokens
        .into_iter()
        .map(|token| {
            let mut token = match token {
                TokenTree::Group(group) => {
                    TokenTree::Group(Group::new(group.delimiter(), same_span(group.stream(), span)))
                }
                token => token,
            };
            token.set_span(span);
            token
        })
        .collect()
}

#[proc_macro]
pub fn generate(input: TokenStream) -> TokenStream {
    let extra = match input.to_string().as_str() {
        "valid" => "",
        "wrong_var" => r#"#[trust::var(name = "misplaced", kind = "Int")] fn misplaced() {}"#,
        "wrong_action" => r#"#[trust::action(name = "Misplaced")] fn misplaced() {}"#,
        "statement_var" => {
            r#"fn misplaced() {
                #[trust::var(name = "misplaced", kind = "Int")] let _state = 0_u64;
            }"#
        }
        other => panic!("unknown same-span fixture {other}"),
    };
    let source = format!(
        r#"
        struct Machine {{
            #[trust::var(name = "first", kind = "Int")] first: u64,
            #[trust::var(name = "second", kind = "Int")] second: u64,
        }}
        impl Machine {{
            #[trust::action(name = "Step")] fn step(&mut self) {{}}
        }}
        {extra}
        "#
    );
    same_span(source.parse().unwrap(), Span::call_site())
}
