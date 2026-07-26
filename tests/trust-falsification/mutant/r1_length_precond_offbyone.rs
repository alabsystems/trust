// TRAP (piece #8, T5 — Le-vs-Lt boundary): the caller passes bound `17` for a
// `[u32; 16]` array. The loop is `0..n` EXCLUSIVE, so the tight precondition is
// `n <= arr__slice_len`; here σ renders `17 <= 16`, which is FALSE ⇒ `¬P[σ]` SAT ⇒
// no flip ⇒ fail-closed. Guards the synthesizer's exclusive-range boundary: with
// n = len the indices are 0..len-1 (in bounds, proves — see the WIN); with
// n = len+1 the last index len overflows. Runtime: `arr[16]` panics.
fn fill(arr: &mut [u32], n: usize) {
    let mut i = 0;
    while i < n {
        arr[i] = 0;
        i += 1;
    }
}

pub fn run() {
    let mut buf = [0u32; 16];
    fill(&mut buf, 17);
}
