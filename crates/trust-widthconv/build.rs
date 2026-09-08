//! Register the verification-session cfg without selecting it here.
//!
//! `trustc` injects `cfg(trust_verify)` only for the session in which native
//! clauses must be retained. A build script must not guess compiler identity,
//! run the compiler recursively, or enable that cfg for an ordinary build.

fn main() {
    println!("cargo::rustc-check-cfg=cfg(trust_verify)");
}
