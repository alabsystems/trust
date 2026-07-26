//! Embed a UAC manifest into `rust-installer.exe` on Windows.
//!
//! Windows' UAC "installer detection" heuristic demands elevation (os error
//! 740, "The requested operation requires elevation") from any unmanifested
//! executable whose file name contains `installer` — which this binary's is.
//! Embedding an `asInvoker` manifest disables the heuristic so dist/install
//! steps can spawn it as a normal user.

fn main() {
    if std::env::var_os("CARGO_CFG_WINDOWS").is_some()
        && std::env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc")
    {
        println!("cargo:rustc-link-arg=/MANIFEST:EMBED");
        println!("cargo:rustc-link-arg=/MANIFESTUAC:level='asInvoker' uiAccess='false'");
    }
}
