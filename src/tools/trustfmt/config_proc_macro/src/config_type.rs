use proc_macro2::TokenStream;

use crate::item_enum::define_config_type_on_enum;

/// Define `config_type` on an enum.
///
/// Structs never had a representable string configuration contract: the old
/// branch called `unimplemented!()` from inside the procedural macro. Emit a
/// normal compiler diagnostic for unsupported input instead of crashing the
/// macro host.
pub fn define_config_type(input: &syn::Item) -> TokenStream {
    let result = match input {
        syn::Item::Enum(en) => define_config_type_on_enum(en),
        other => Err(syn::Error::new_spanned(
            other,
            "#[config_type] supports enums only",
        )),
    };
    result.unwrap_or_else(syn::Error::into_compile_error)
}
