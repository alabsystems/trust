fn main() {
    // Cargo's stock compiler must know that this cfg belongs to Trust, but a
    // build script must never decide whether verification is active. Trust's
    // compiler injects `cfg(trust_verify)` from the authenticated session; the
    // `trust_contract_fn!` invocations in `src/lib.rs` select on it.
    println!("cargo::rustc-check-cfg=cfg(trust_verify)");
}
