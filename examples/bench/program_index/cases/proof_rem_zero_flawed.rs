// Proof-design fixture: minimal flawed remainder-by-zero obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn remainder_unchecked(x: u32, y: u32) -> u32 {
    x % y
}

fn main() {
    let _ = remainder_unchecked(10, 3);
}
