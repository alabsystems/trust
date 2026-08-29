// Test-only source preparation for the frozen MIR differential.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use std::path::PathBuf;

fn main() {
    const SOURCE: &str = "src/mir_differential.rs";
    println!("cargo:rerun-if-changed={SOURCE}");

    let source = std::fs::read_to_string(SOURCE).expect("read frozen MIR differential source");
    let mut generated = String::with_capacity(source.len());
    let mut in_module_docs = true;
    for line in source.split_inclusive('\n') {
        if in_module_docs && line.starts_with("//!") {
            generated.push_str("//");
            generated.push_str(&line[3..]);
        } else {
            in_module_docs = false;
            generated.push_str(line);
        }
    }

    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"))
        .join("mir_differential_without_inner_docs.rs");
    std::fs::write(out, generated).expect("write test-only MIR differential source");
}
