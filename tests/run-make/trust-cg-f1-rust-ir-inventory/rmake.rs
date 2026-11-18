//! Trust: the F1 inventory reads an exact conserved Rust IR leaf, while an
//! otherwise identical source body with a named constant keeps ordinary
//! inventory processing. This checks the actual current compiler hook, not a
//! replayed module or a diagnostic count used as proof authority.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc, serde_json};

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
    // D28 precedes MIR's semantic pointer checks. The inventory must retain
    // their actual panic dependencies even when the earlier IR is call-free.
    rfs::write(
        "raw_inventory.rs",
        "#[unsafe(no_mangle)] pub unsafe fn raw_load(p: *const u32) -> u32 { unsafe { *p } }",
    );
    let raw = rustc()
        .input("raw_inventory.rs")
        .crate_name("raw_inventory")
        .crate_type("rlib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Copt-level=0")
        .arg("-Zmir-opt-level=0")
        .arg("-Zunstable-options")
        .arg("-Zub-checks=yes")
        .arg("-Ztrust-ir-lower")
        .arg("-Zchecksum-hash-algorithm=sha256")
        .arg("-Ztrust-instance-census=raw-inventory.jsonl")
        .arg("-Ztrust-verify=off")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .env_remove("TRUST_NO_VERIFY")
        .env("RUSTC_LOG", LOG)
        .run_unchecked();
    assert!(
        !raw.stderr_utf8().contains(ROUTE),
        "a raw dereference cannot replace late pointer-check dependencies: {}",
        raw.stderr_utf8()
    );
    // A non-generic external helper need not be codegened in this crate, so
    // print-mono-items is not its denominator. Inspect the existing collector's
    // typed dependency observations, including the actual owner and call site.
    let rows: Vec<serde_json::Value> = rfs::read_to_string("raw-inventory.jsonl")
        .lines()
        .map(|line| serde_json::from_str(line).expect("actual instance census JSONL"))
        .collect();
    let snapshot = rows.iter().find(|row| row["event"] == "mono_snapshot")
        .expect("actual collector snapshot must exist before backend refusal");
    let nodes = snapshot["dependency_nodes"].as_array().unwrap();
    let owner = nodes.iter().find(|node| node["definition_is_local"] == true
        && node["def"].as_str().is_some_and(|name| name.ends_with("::raw_load")))
        .expect("actual raw-load instance owner");
    let panic = nodes.iter().find(|node| node["def"].as_str()
        .is_some_and(|name| name.ends_with("::panic_misaligned_pointer_dereference")))
        .expect("actual alignment panic dependency node");
    let used_owner = snapshot["dependency_owners"].as_array().unwrap().iter()
        .find(|row| row["item"] == owner["id"] && row["collection_mode"] == "used")
        .expect("actual raw-load used-item visit");
    assert!(snapshot["dependency_occurrences"].as_array().unwrap().iter().any(|edge|
        edge["owner"] == used_owner["id"] && edge["target"] == panic["id"]
            && edge["kind"] == "instance-use" && edge["site"] == "language-item"
            && edge["origin"] == "mir" && edge["mode"] == "used"),
        "raw-load inventory must retain its actual alignment panic edge: {snapshot}");
    let pointer = compile(
        "#[unsafe(no_mangle)] pub fn same_cell() -> bool { \
         let value = 7u32; core::ptr::eq(&value, &value) }",
        "pointer_inventory",
    );
    assert!(pointer.contains(ROUTE), "the scalar-cell inventory hook did not run: {pointer}");

}
