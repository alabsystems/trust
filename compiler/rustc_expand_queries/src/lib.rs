// Trust (D21): this crate no longer names `proc_macro::bridge` (the derive client type
// is `rustc_expand`'s, in-process or isolated), so upstream's `proc_macro_internals`
// gate and its lint allowance are gone.

mod derive;

pub fn setup_callbacks() {
    rustc_expand::proc_macro::EXPAND_DERIVE_MACRO_CACHED
        .swap(&(derive::expand_derive_macro_cached as _));
}

pub fn provide(providers: &mut rustc_middle::query::Providers) {
    providers.derive_macro_expansion = derive::derive_macro_expansion;
}
