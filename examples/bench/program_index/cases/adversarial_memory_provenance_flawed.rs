// Adversarial fixture: raw pointer access is detached from slice bounds.
//
// The main uses an in-bounds index, but callers can violate provenance/bounds.

fn byte_at_unchecked(data: &[u8], idx: usize) -> u8 {
    unsafe { *data.as_ptr().add(idx) }
}

fn main() {
    let data = [4, 8, 15, 16];
    let _ = byte_at_unchecked(&data, 2);
}
