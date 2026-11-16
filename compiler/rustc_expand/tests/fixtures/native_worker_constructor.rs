//! Real DSO initializer control: no policy admission is inferred from this fixture.
#![feature(
    proc_macro_internals,
    proc_macro_span,
    proc_macro_diagnostic,
    proc_macro_expand,
    proc_macro_tracked_env,
    proc_macro_tracked_path
)]
extern crate proc_macro;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU8, Ordering};

use proc_macro::{self as pm, TokenStream};
#[path = "../../src/proc_macro_server/isolation/dispatch/tests/native_client_methods.rs"]
mod native_client_methods;
static INITIALIZER: AtomicU8 = AtomicU8::new(0);
static CONSTRUCTOR_TMPDIR: OnceLock<String> = OnceLock::new();
#[used]
#[unsafe(link_section = "__DATA,__mod_init_func")]
static BEFORE_ENTRY: extern "C" fn() = initializer;
extern "C" fn initializer() {
    use std::fmt::Write;
    use std::os::unix::ffi::OsStrExt;
    let directory = std::env::temp_dir();
    let mut encoded = String::new();
    for byte in directory.as_os_str().as_bytes() {
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    CONSTRUCTOR_TMPDIR.set(encoded).unwrap();
    let path =
        directory.join(".ubd").join(format!("trust-native-constructor-{}", std::process::id()));
    let state = match std::fs::OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(file) => {
            drop(file);
            let _ = std::fs::remove_file(&path);
            2
        }
        Err(error) if matches!(error.raw_os_error(), Some(1 | 13)) => 1,
        Err(_) => 3,
    };
    INITIALIZER.store(state, Ordering::Release);
}
fn initializer_was_denied() {
    assert_eq!(
        INITIALIZER.load(Ordering::Acquire),
        1,
        "real DSO initializer must have executed and received a policy denial before entry"
    );
}
#[proc_macro]
pub fn first_declaration(_: TokenStream) -> TokenStream {
    let state = INITIALIZER.load(Ordering::Acquire);
    let result = if state == 1 {
        "selected_first_declaration".to_owned()
    } else {
        format!("wrong_constructor_state_{state}")
    };
    format!("{result}_tmp_{}", CONSTRUCTOR_TMPDIR.get().expect("initializer ran")).parse().unwrap()
}
#[proc_macro]
pub fn second_declaration(input: TokenStream) -> TokenStream {
    initializer_was_denied();
    native_client_methods::all_methods(input)
}
