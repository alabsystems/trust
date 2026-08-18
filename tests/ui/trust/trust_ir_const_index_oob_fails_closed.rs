//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//
// Trust (#191) regression: a CONSTANT array index is not automatically in bounds.
//
// `C[10]` on a `[u32; 5]` is a guaranteed Rust panic — built MIR emits a bounds `Assert` and the
// function diverges. The producer's constant-index fast path used to emit a bare
// `ExtractField 10` with no check at all, turning a diverging function into a value-returning one,
// and recorded the body `lowered` with `unsupported: []` — i.e. CLEAN. The module validator caught
// it as `FieldAccessInvalid`; no differential could, because the interpreter is not run on these
// bodies.
//
// The arm's original justification was that "the interpreter TRAPS on out-of-bounds". That is true
// of the DYNAMIC index path, which does reach `eval_extract_element` — but nothing forces this
// module through the interpreter, and codegen would simply take the offset. So the constant path
// now fails the body closed until the bounds `Assert` is modelled.
//
// `check-pass` is the whole point: failing CLOSED is a lowering refusal, never a compile error.
// Trust compiles all valid Rust identically.

const C: [u32; 5] = [0, 0, 0, 0, 0];

// Out of bounds — must NOT lower to a bare field read.
pub fn oob() -> u32 {
    C[10]
}

// Zero-length array: every index is out of bounds.
const EMPTY: [u32; 0] = [];

pub fn oob_empty() -> u32 {
    EMPTY[0]
}

// The in-bounds twin must keep lowering exactly as before — the gate is a bounds test, not a
// blanket refusal of constant indices.
pub fn in_bounds() -> u32 {
    C[4]
}

fn main() {}
