// Proof-design fixture: minimal guarded slice-index bounds obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// bounds proof surface without std I/O noise.

fn slice_lookup_guarded(data: &[u32], idx: usize) -> u32 {
    if idx < data.len() {
        data[idx]
    } else {
        0
    }
}

fn main() {
    let data = [1, 2, 3, 4];
    let _ = slice_lookup_guarded(&data, 2);
    let _ = slice_lookup_guarded(&data, 8);
}
