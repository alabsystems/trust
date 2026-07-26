// Proof-design fixture: unguarded range can exceed slice bounds.
//
// This stays free of formatting and allocation so the verifier sees the
// range-bounds proof surface without std I/O noise.

fn window_len_unchecked(data: &[u32], start: usize, end: usize) -> usize {
    data[start..end].len()
}

fn main() {
    let data = [1, 2, 3, 4];
    let _ = window_len_unchecked(&data, 1, 3);
}
