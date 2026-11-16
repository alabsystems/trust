//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ run-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Drop-in compat pin (HOLE B / Option Y, 2026-09-14). A dynamic
//! `{:width$}`/`{:.precision$}` count is a RUNTIME-CHECKED obligation: the fmt
//! machinery range-checks the caller-supplied width at runtime, so the program
//! has vanilla-Rust semantics and BUILDS AND RUNS under the default policy —
//! whether or not a `println!` is present.
//!
//! The former `print_gap_masks_unproved_own_obligation` gate REFUSED this valid
//! program (an over-strict drop-in break, since Trust must compile all valid Rust
//! identically). Removing that gate restores it; the print grace now withholds
//! tolerance only for a FAIL-CLOSED masked dispatch (`write!` into a sink, a
//! spoofed `_print`), never for a caller's own retained-runtime-check panic.
fn main() {
    let w: usize = std::hint::black_box(4);
    // Prints "[   7]" (7 right-justified in a runtime-width field of 4) and exits 0.
    println!("[{:w$}]", 7i32);
}
