// TRAP (piece #8, T1 — INV-2 load-bearing): the caller passes a SHORTER array
// (`[u32; 8]`) than the loop bound (`16`). The σ length-renderer produces the
// caller obligation `16 <= 8`, which is FALSE — `¬P[σ]` is SAT — so the caller
// does NOT discharge P and the R1 flip is REJECTED. `fill` keeps its honest Failed
// verdict ⇒ build error (fail-closed), avoiding the runtime OOB at `arr[8]`. This
// proves σ renders the ACTUAL length (8), not the formal — if it flipped, INV-2
// would be broken. Runtime: `arr[8]` on a len-8 array panics (index out of bounds).
fn fill(arr: &mut [u32], n: usize) {
    let mut i = 0;
    while i < n {
        arr[i] = 0;
        i += 1;
    }
}

pub fn run() {
    let mut buf = [0u32; 8];
    fill(&mut buf, 16);
}
