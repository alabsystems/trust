//! Trust: the F1 inventory reads an exact conserved Rust IR leaf, while an
//! otherwise identical source body with a named constant keeps ordinary
//! inventory processing. This checks the actual current compiler hook, not a
//! replayed module or a diagnostic count used as proof authority.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const ROUTE: &str = "F1 inventory read from exact conserved Rust IR";
const LOG: &str =
    "rustc_codegen_trust_cg::trust_ir_frontend::clean_inventory::rust_inventory=info";

fn compile(source: &str, name: &str) -> String {
    let input = format!("{name}.rs");
    rfs::write(&input, source);
    rustc()
        .input(input)
        .crate_name(name)
        .crate_type("rlib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .env_remove("TRUST_NO_VERIFY")
        .env("RUSTC_LOG", LOG)
        .run()
        .stderr_utf8()
}

fn main() {
    let direct = compile(
        "#[unsafe(no_mangle)] pub fn bits(x: u64, y: u64) -> u64 { (!x & y) ^ 85 }",
        "direct_inventory",
    );
    assert!(direct.contains(ROUTE), "the actual Rust IR inventory hook did not run: {direct}");
    let named = compile(
        "const MASK: u64 = 85; #[unsafe(no_mangle)] pub fn bits(x: u64, y: u64) -> u64 { (!x & y) ^ MASK }",
        "named_const_inventory",
    );
    assert!(
        !named.contains(ROUTE),
        "the source guard must retain required-constant processing: {named}"
    );
}
