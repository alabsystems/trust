// WIN (piece #8 — length-relationship preconditions, case a): a private `fill`
// whose bounds obligation `arr[i]` (i in 0..n) flips to Proved via the SYNTHESIZED
// precondition `P = n <= arr__slice_len`. The only caller passes a fixed-size
// `[u32; 16]` array and the loop bound `16`, so the σ length-renderer produces the
// caller obligation `16 <= 16` (a tautology) — R1 certifies F-under-P + discharges
// every caller ⇒ the flip is admitted and `fill` proves NON-VACUOUSLY (2 proved,
// 0 failed, 0 unknown). Demonstrates INV-2 (σ renders the EXACT actual length, read
// off the immutable array type at the array→slice unsize cast) and the connectedness
// invariant INV-4 (P's vars {n, arr__slice_len} ⊆ V's vars).
fn fill(arr: &mut [u32], n: usize) {
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
