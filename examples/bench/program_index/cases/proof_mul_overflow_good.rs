// Proof-design fixture: minimal guarded multiplication-overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn multiply_guarded(a: u32, b: u32) -> u32 {
    if a <= 65_535 && b <= 65_535 {
        a * b
    } else {
        0
    }
}

fn main() {
    let _ = multiply_guarded(20, 30);
    let _ = multiply_guarded(u32::MAX, 2);
}
