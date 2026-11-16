//@ trust-ladder: verifies
//@ trust-ladder-row: panic-free relative to its
//@ trust-ladder-crate-type: bin
//! D1 increment 2 (2026-09-25): `println!` of a `#[derive(Debug)]` value — the
//! derived impl is writer-relative and error-transparent (recognizer version 2),
//! and `println!` is a std sink that supplies the writer. Also `{:#?}`, which
//! runs core's `PadAdapter` over that writer. Measured BEFORE on the stage-1
//! snapshot `43b8fe6ab`: refuses ("formatted through a user" on `main`, "strict
//! verification failed" on the impl). AFTER is PREDICTED until the lead's build
//! records it; the needle is the writer-relative disclosure on the impl.
#[derive(Debug)]
pub enum ConfigError { Missing(&'static str), Invalid { key: &'static str, got: u32 } }
fn main() {
    println!("{:?}", ConfigError::Missing("port"));
    println!("{:#?}", ConfigError::Invalid { key: "port", got: std::hint::black_box(0) });
}
