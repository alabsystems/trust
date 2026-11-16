//! Trust (W6): one crate, two languages, handed to the trust-ir CODEGEN
//! frontend. `calls_clean` is a Rust body whose call edge IR-5 re-points at
//! the appended Clean-origin row; under `-Ztrust-cg-frontend=trust-ir` the
//! Module -> LIR converter would otherwise splice that Clean body straight into
//! the Rust caller's object. The producer gate must refuse it BY NAME — never
//! an ICE, never a silent splice. `rust_only` is the control: no Clean edge.
#![crate_name = "clean_below_gate"]

mod m {
    clean {
        def cleanWsum (a : UInt64) (b : UInt64) : UInt64 := a + b
    }
}

#[inline(never)]
pub fn calls_clean(x: u64) -> u64 {
    m::cleanWsum(x, 1)
}

// A pure bitwise body with NO call: it lowers through the trust-ir codegen
// frontend cleanly, so the ONLY refusal in this crate is the Clean-origin edge
// in `calls_clean` — the gate under test, not an unrelated unsupported-Call.
#[inline(never)]
pub fn rust_only(x: u64) -> u64 {
    x ^ 0x55
}
