//@ fn-ptr-witness-gap: proved-plus-unknown-no-gap
//@ fn-ptr-witness: refuses
//! BOUNDARY CONTROL, and a correction to two of my own wrong readings.
//!
//! An explicit TAIL call through a fn pointer ALREADY REFUSES — "native typed
//! TrustIr lowering did not complete, so the panic-freedom of an unmodeled
//! construct could not be established". So the hole is the ordinary call form
//! only, and this row marks that edge.
//!
//! TWO ERRORS THIS ROW CAUGHT, both mine, both from reading truncated output:
//!   1. I first wrote `pub fn tcall(f: fn(u32)->u32, x: u32) -> u32 { become f(x) }`,
//!      which is not valid Rust at all — `become` requires the callee's
//!      signature to match the caller's, and rustc says "mismatched signatures".
//!      I had read its empty JSON as "produces no rows", when it had simply
//!      failed to compile.
//!   2. Having fixed the program, the row is not a hole either: it refuses.
//! A zero is a fact about the instrument until the instrument has produced a
//! non-zero, and an empty JSON is a fact about the COMPILE until the compile has
//! been shown to succeed.
#![feature(explicit_tail_calls)]
fn id(x: u32) -> u32 { x }
static F: fn(u32) -> u32 = id;
pub fn tcall(x: u32) -> u32 { become F(x) }
