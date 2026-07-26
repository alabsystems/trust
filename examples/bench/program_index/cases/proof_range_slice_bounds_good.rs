// Proof-design fixture: range bounds guard a slice operation.
//
// This stays free of formatting and allocation so the verifier sees the
// range-bounds proof surface without std I/O noise.

fn window_len_guarded(data: &[u32], start: usize, end: usize) -> usize {
    if start <= end && end <= data.len() {
        data[start..end].len()
    } else {
        0
    }
}

fn main() {
    let data = [1, 2, 3, 4];
    let _ = window_len_guarded(&data, 1, 3);
    let _ = window_len_guarded(&data, 3, 1);
    let _ = window_len_guarded(&data, 0, 8);
}
