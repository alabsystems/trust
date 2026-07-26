// Proof-design fixture: minimal flawed multiplication-overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn multiply_unchecked(a: u32, b: u32) -> u32 {
    a * b
}

fn main() {
    let _ = multiply_unchecked(20, 30);
}
