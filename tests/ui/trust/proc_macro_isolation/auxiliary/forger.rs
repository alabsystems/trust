//! Macros that try what a hostile proc macro would: speak in the compiler's
//! voice on its stderr, plant a file where the compiler writes its output, and
//! look at what the process they run in holds open. Each reports what happened
//! in its expansion, so the test program can assert it.
extern crate proc_macro;

use std::io::Write;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::path::PathBuf;

use proc_macro::TokenStream;

/// Write one complete JSON diagnostic to standard error, exactly as rustc
/// writes its own under `--error-format=json`. Whoever reads the compiler's
/// stderr cannot tell this line from a real diagnostic.
#[proc_macro]
pub fn forge_compiler_message(_input: TokenStream) -> TokenStream {
    let forged = concat!(
        r#"{"$message_type":"diagnostic","message":"forged by a proc macro: "#,
        r#"all obligations proved","code":null,"level":"warning","spans":[],"#,
        r#""children":[],"rendered":"warning: forged by a proc macro: "#,
        r#"all obligations proved\n\n"}"#,
    );
    let mut stderr = std::io::stderr().lock();
    let _ = writeln!(stderr, "{forged}");
    let _ = stderr.flush();
    // Standard output is the other voice a build tool listens to.
    println!("{forged}");
    TokenStream::new()
}

/// Try to create `planted-by-macro.rmeta` in `$FORGE_DIR`, the directory this
/// compilation writes its output to, and a scratch file in the temporary
/// directory. Expands to `(planted, scratch_written)`.
///
/// The expansion is an error, not `false`, when `$FORGE_DIR` is not an existing
/// directory: a test that pointed the macro at nothing would prove nothing.
#[proc_macro]
pub fn write_into_output_dir(_input: TokenStream) -> TokenStream {
    let Some(directory) = std::env::var_os("FORGE_DIR").map(PathBuf::from) else {
        return r#"compile_error!("FORGE_DIR is not set");"#.parse().unwrap();
    };
    if !directory.is_dir() {
        return r#"compile_error!("FORGE_DIR is not a directory");"#.parse().unwrap();
    }
    let planted = std::fs::write(directory.join("planted-by-macro.rmeta"), b"forged").is_ok();
    let scratch = std::env::temp_dir().join(format!("forger-scratch-{}", std::process::id()));
    let scratch_written = std::fs::write(&scratch, b"scratch").is_ok();
    let _ = std::fs::remove_file(&scratch);
    format!("({planted}, {scratch_written})").parse().unwrap()
}

/// Expands to a string literal listing this process's open descriptors, as
/// `number:kind` joined by commas, where kind is `socket`, `null` (the null
/// device), `directory` or `other`. The directory this listing itself holds
/// open is left out.
#[proc_macro]
pub fn open_descriptors(_input: TokenStream) -> TokenStream {
    let null = std::fs::metadata("/dev/null").map(|metadata| metadata.rdev()).ok();
    let mut numbers: Vec<u32> = std::fs::read_dir("/dev/fd")
        .unwrap()
        .filter_map(|entry| entry.ok()?.file_name().to_str()?.parse().ok())
        .collect();
    numbers.sort_unstable();
    let mut listing = Vec::new();
    for number in numbers {
        // The listing's own descriptor is closed by now and no longer resolves.
        let Ok(metadata) = std::fs::metadata(format!("/dev/fd/{number}")) else {
            continue;
        };
        let kind = metadata.file_type();
        let kind = if kind.is_socket() {
            "socket"
        } else if kind.is_char_device() && Some(metadata.rdev()) == null {
            "null"
        } else if kind.is_dir() {
            "directory"
        } else {
            "other"
        };
        listing.push(format!("{number}:{kind}"));
    }
    format!("{:?}", listing.join(",")).parse().unwrap()
}

/// A derive that panics with a message, as a macro reports a misuse.
#[proc_macro_derive(Explode)]
pub fn derive_explode(_input: TokenStream) -> TokenStream {
    panic!("the Explode derive always panics");
}
