// Adversarial fixture: loop count is not tied to the slice length.
//
// The main uses a safe count, but the helper is flawed for larger counts.

fn prefix_checksum_unchecked(data: &[u32], count: usize) -> u32 {
    let mut i = 0;
    let mut acc = 0u32;
    while i < count {
        acc = acc.wrapping_add(data[i]);
        i += 1;
    }
    acc
}

fn main() {
    let data = [1, 3, 5, 7];
    let _ = prefix_checksum_unchecked(&data, 3);
}
