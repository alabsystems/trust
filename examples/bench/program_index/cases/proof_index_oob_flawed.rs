// Proof-design fixture: minimal flawed array-index bounds obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// bounds proof surface without std I/O noise.

fn lookup_unchecked(data: [u32; 4], idx: usize) -> u32 {
    data[idx]
}

fn main() {
    let data = [1, 2, 3, 4];
    let _ = lookup_unchecked(data, 2);
}
