//! A derive nobody has to invoke. Its dylib carries a load-time initializer,
//! which the dynamic loader runs at `dlopen` — before rustc looks up a single
//! macro. It records that it ran in the file `PM_TCB_SENTINEL` names. This is
//! the shape of reports/2026-09-28-proc-macro-boundary-b2/probes/initializer-macro.
extern crate proc_macro;
use proc_macro::TokenStream;

#[cfg(target_vendor = "apple")]
#[used]
#[link_section = "__DATA,__mod_init_func"]
static PM_TCB_INIT: extern "C" fn() = pm_tcb_init;

#[cfg(not(target_vendor = "apple"))]
#[used]
#[link_section = ".init_array"]
static PM_TCB_INIT: extern "C" fn() = pm_tcb_init;

extern "C" fn pm_tcb_init() {
    if let Some(path) = std::env::var_os("PM_TCB_SENTINEL") {
        let _ = std::fs::write(path, b"initializer ran at dlopen\n");
    }
}

#[proc_macro_derive(Quiet)]
pub fn derive_quiet(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}
