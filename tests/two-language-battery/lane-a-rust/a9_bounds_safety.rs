//@ battery-lane: A-rust
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A (Rust, native clauses) — BOUNDS SAFETY: index obligations discharged
//! by contract instead of by a runtime check.
//!
//! This is the payoff case for the whole exercise. `xs[i]` in Rust is a
//! runtime bounds check and a potential panic; under verification it is an
//! obligation, and a contract that discharges it turns "this cannot panic" from
//! a claim into a result. Each function below discharges its index obligation
//! by a DIFFERENT route, which is why they are one file:
//!
//!   * `element_at`  — from the function PRECONDITION.
//!   * `window_end`  — from the PATH CONDITION (no index at all: it computes a
//!                     range end that makes the caller's slicing total).
//!   * `xor_fold`    — from the LOOP INVARIANT.
//!
//! The collection vocabulary used here is the bounded model that
//! `tests/ui/trust/native_loop_collection_semantics.rs` exercises. Shared
//! slice/fixed-array reads and exact exclusive Store/Select transitions are
//! admitted; retained aliases, reseats, collection-bearing calls, and other
//! mutable shapes fail closed. This fixture uses only shared slices:
//! `.len()` and `.is_empty()` admit an Array-sorted base
//! (`crates/trust-types/src/spec_render.rs:404-420`), and a slice parameter's
//! `xs.len()` reaches the query as the synthetic pointer-sized `xs_len` leaf
//! (`compiler/rustc_mir_transform/src/trust_contract_query.rs:519-533`).

/// Read one element with the bound PROVED rather than checked.
///
/// The precondition is not documentation and not a debug assertion: it is the
/// entire discharge of the `xs[i]` panic obligation. Delete it and the function
/// must be refuted, because `i` is otherwise unconstrained. This is the
/// smallest honest statement of what a verified indexing API looks like — the
/// caller owes the bound, and the callee owes nothing.
pub fn element_at(xs: &[u32], i: usize) -> u32
    requires i < xs.len()
{
    xs[i]
}

/// End index of a window into `xs`, clamped so that `&xs[start..result]` is
/// always a legal slicing.
///
/// Every arithmetic operation is guarded by the branch or precondition above
/// it: `xs.len() - start` cannot wrap because `start <= xs.len()`, and
/// `start + count` cannot overflow because it runs only where
/// `count <= xs.len() - start`. The postcondition is the half the caller needs
/// — a range whose end precedes its start is the other way to panic on a
/// slicing, and `result >= start` rules it out. `result <= xs.len()` is the
/// remaining half, and it is deliberately NOT claimed here: it would put the
/// collection leaf on both sides of the postcondition, which is a different
/// (and unmeasured) obligation from the scalar one this file is pinning.
pub fn window_end(xs: &[u32], start: usize, count: usize) -> usize
    requires start <= xs.len()
    ensures result >= start
{
    let room = xs.len() - start;
    if count > room { xs.len() } else { start + count }
}

/// XOR fold over a byte frame — a one-byte checksum.
///
/// The loop invariant is doing real work: `i <= xs.len()` is what makes
/// `xs[i]` in bounds when combined with the loop guard, and it is the form
/// `a8_NEG_wrong_invariant.rs` gets wrong. `xs.len() - i` is the measure, in
/// the grammar position between condition and body that vanilla Rust rejects
/// (`tests/ui/trust/native_loop_clauses.rs:13-17`).
///
/// The body is XOR rather than addition on purpose. An accumulating `+=` over
/// an unbounded slice carries an overflow obligation that NO invariant on `i`
/// can discharge — the bound would have to be on the element sum — so an
/// arithmetic fold would silently turn this from a bounds-safety measurement
/// into an overflow measurement. XOR is total on `u8`, which leaves the index
/// obligation as the only thing this function is asking about.
pub fn xor_fold(xs: &[u8]) -> u8 {
    let mut acc = 0u8;
    let mut i = 0usize;
    while i < xs.len()
        invariant i <= xs.len()
        decreases xs.len() - i
    {
        acc ^= xs[i];
        i += 1;
    }
    acc
}
