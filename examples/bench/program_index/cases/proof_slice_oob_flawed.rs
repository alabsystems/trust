// Proof-design fixture: minimal flawed slice-index bounds obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// bounds proof surface without std I/O noise.

fn slice_lookup_unchecked(data: &[u32], idx: usize) -> u32 {
    data[idx]
}

fn main() {
    let data = [1, 2, 3, 4];
    let _ = slice_lookup_unchecked(&data, 2);
}
