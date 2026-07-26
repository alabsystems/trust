// Adversarial fixture: raw pointer access stays within slice provenance.
//
// The explicit pointer operation keeps fat-pointer/provenance obligations in
// the corpus without relying on compiler or solver internals.

fn byte_at(data: &[u8], idx: usize) -> u8 {
    if idx < data.len() {
        unsafe { *data.as_ptr().add(idx) }
    } else {
        0
    }
}

fn main() {
    let data = [4, 8, 15, 16];
    let _ = byte_at(&data, 2);
    let _ = byte_at(&data, 9);
}
