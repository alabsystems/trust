// Provenance source for `unsupported-row-polarity`. Extracted with the stage2
// `trustc` (see PROVENANCE.md) — the JSON beside this file is the compiler's own
// MIR, not hand-written.
//
// `&v[..end]` over an owned `Vec` gives `panic_calls`'s soft-len arm a length it
// cannot derive, so it DECLINES the bounds obligation with an `UnsupportedMir`
// row. The `ensures` clause is discharged by the kernel, so this function's
// certification turns entirely on how the gate reads that declined row.
//
// The body PANICS whenever `end > v.len()`.
#![allow(dead_code)]
#![crate_type = "lib"]

pub fn vec_range_index_with_ensures(v: Vec<u32>, end: usize) -> u32
    ensures result < 8
{
    let _s = &v[..end];
    7
}

// CONTROL: the SAME contract with no declined row. The gate certifies this one,
// which is what makes the negative verdict on the function above a statement
// about the declined row rather than about the gate refusing everything.
pub fn const_return_with_ensures(y: u32) -> u32
    ensures result < 8
{
    let _ = y;
    7
}
