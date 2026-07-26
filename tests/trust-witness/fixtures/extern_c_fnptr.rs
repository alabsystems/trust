// SCOPE WIDENING (was audit rank 1): a non-Rust-ABI fn-pointer TYPE in the body.
// The tag-14 encoding originally dropped the fn-ptr ABI and decode rebuilt Rust, so
// this reconstructed as `fn(u32)->u32` (Rust ABI), the checker ACCEPTed the wrong
// type, and MIR/borrowck equate ICE'd. The lock-in conservatively ESCAPED such
// types (MISS). Scope widening (schema v5) now round-trips the ABI faithfully, so
// this root is MINTED again and warm replay ACCEPTs it byte-identically.
//
// NB: `p`'s type is INFERRED (no `: extern "C" fn(..)` annotation) — an explicit
// annotation would populate user_provided_types, which mintable() excludes for an
// unrelated reason, so the fixture would not exercise the fn-ptr ABI path.
pub extern "C" fn a(x: u32) -> u32 {
    x + 1
}
pub extern "C" fn b(x: u32) -> u32 {
    x + 2
}

pub fn choose(c: bool, n: u32) -> u32 {
    let p = if c { a } else { b };
    p(n)
}
