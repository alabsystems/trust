//! A derive that tries, twice, to leave a mark outside the compiler's control:
//! a load-time initializer (the loader runs it at `dlopen`, before any macro is
//! looked up) and the expansion itself each write a file beside the path
//! `PM_ISO_SENTINEL` names. Loaded in process both succeed. In the isolated
//! worker neither can: the path is outside the worker's private directory.
//!
//! The expansion is real work the consumer depends on: `FIELDS` is the number
//! of named fields, which the consumer asserts at compile time.
extern crate proc_macro;
use proc_macro::{Delimiter, Spacing, TokenStream, TokenTree};

fn mark(suffix: &str) {
    if let Some(path) = std::env::var_os("PM_ISO_SENTINEL") {
        let mut path = path;
        path.push(suffix);
        let _ = std::fs::write(path, b"ran\n");
    }
}

#[used]
#[link_section = "__DATA,__mod_init_func"]
static PM_ISO_INIT: extern "C" fn() = pm_iso_init;

extern "C" fn pm_iso_init() {
    mark("-init");
}

#[proc_macro_derive(Counted)]
pub fn derive_counted(input: TokenStream) -> TokenStream {
    mark("-expand");
    let mut name = None;
    let mut fields = 0usize;
    let mut after_struct = false;
    for tree in input {
        match tree {
            TokenTree::Ident(ident) if after_struct => {
                name = Some(ident.to_string());
                after_struct = false;
            }
            TokenTree::Ident(ident) => after_struct = ident.to_string() == "struct",
            TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                fields = group
                    .stream()
                    .into_iter()
                    .filter(|tree| {
                        matches!(tree, TokenTree::Punct(p)
                            if p.as_char() == ':' && p.spacing() == Spacing::Alone)
                    })
                    .count();
            }
            _ => {}
        }
    }
    let name = name.expect("Counted is derived on a struct");
    format!("impl {name} {{ pub const FIELDS: usize = {fields}; }}").parse().unwrap()
}
