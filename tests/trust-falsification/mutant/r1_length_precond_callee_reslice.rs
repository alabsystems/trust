// TRAP (piece #8, T2 — INV-1): the callee RESLICES its slice param `arr` to a
// shorter view (`arr = &mut arr[..1]`) before the indexed loop. `arr__slice_len`
// would then denote the ORIGINAL caller length (16) while the indexed view is
// length 1 — a false PROVE if admitted. The piece #8 gate's INV-1 stability check
// (`slice_param_length_is_stable`) sees the whole-local reassign / mutable reborrow
// of the param fat pointer and does NOT admit `arr__slice_len`, so the synthesized
// P is dropped ⇒ no flip ⇒ fail-closed. Runtime: `arr[1]` on the len-1 reslice
// panics. If this flips, INV-1 is broken.
fn fill(arr: &mut [u32], n: usize) {
    let arr = &mut arr[..1];
    let mut i = 0;
    while i < n {
        arr[i] = 0;
        i += 1;
    }
}

pub fn run() {
    let mut buf = [0u32; 16];
    fill(&mut buf, 16);
}
