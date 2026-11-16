// Only target properties belong to the engine. Checkout labels and manuals
// belong to the executable package and must not invalidate this action.
#[expect(clippy::disallowed_methods, reason = "Targo supplies TARGET to build scripts")]
fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!(
        "cargo:rustc-env=RUST_HOST_TARGET={}",
        std::env::var("TARGET").unwrap()
    );
}
