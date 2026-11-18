//! Exercise the compiler's exact pure inventory reader as an ordinary Trust
//! component. Source identity, THIR screening and the collector hook are checked
//! by the source-compiler run-make fixture, not by this pure reader's tests.

#[path = "../../../compiler/rustc_codegen_trust_cg/src/trust_ir_frontend/clean_inventory/rust_inventory/ir.rs"]
mod inventory;
