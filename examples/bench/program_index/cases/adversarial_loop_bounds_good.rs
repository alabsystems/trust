// Adversarial fixture: loop bound is clamped to the slice length.
//
// This targets loop-carried bounds reasoning without std formatting noise.

fn prefix_checksum(data: &[u32], count: usize) -> u32 {
    let limit = if count <= data.len() { count } else { data.len() };
    let mut i = 0;
    let mut acc = 0u32;
    while i < limit {
        acc = acc.wrapping_add(data[i]);
        i += 1;
    }
    acc
}

fn main() {
    let data = [1, 3, 5, 7];
    let _ = prefix_checksum(&data, 3);
    let _ = prefix_checksum(&data, 99);
}
