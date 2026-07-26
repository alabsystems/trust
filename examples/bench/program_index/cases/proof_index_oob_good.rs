// Proof-design fixture: minimal guarded array-index bounds obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// bounds proof surface without std I/O noise.

fn lookup_guarded(data: [u32; 4], idx: usize) -> u32 {
    if idx < 4 {
        data[idx]
    } else {
        0
    }
}

fn main() {
    let data = [1, 2, 3, 4];
    let _ = lookup_guarded(data, 2);
    let _ = lookup_guarded(data, 8);
}
