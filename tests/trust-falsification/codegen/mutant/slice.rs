#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// MUTANT: slice indexing is OUTSIDE trust-cg's verified scalar fragment, so the
// lowering does not faithfully round-trip. Trust must REJECT
// `#[trust::verified_codegen]` (build error) rather than vacuously accept it —
// proving the verified-codegen guarantee is non-vacuous.
#[trust::verified_codegen]
pub fn first(s: &[u32]) -> u32 { s[0] }
