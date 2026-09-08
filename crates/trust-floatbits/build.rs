//! Register the compiler-owned verification cfg with Cargo's cfg lint.
//!
//! This build script does not probe a compiler and never selects the contract
//! surface. Trust injects `cfg(trust_verify)` from the authenticated compiler
//! session; stock and bootstrap compilers leave it unset.

fn main() {
    println!("cargo::rustc-check-cfg=cfg(trust_verify)");
}
