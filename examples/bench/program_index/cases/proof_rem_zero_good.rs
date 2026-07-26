// Proof-design fixture: minimal guarded remainder-by-zero obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn remainder_guarded(x: u32, y: u32) -> u32 {
    if y == 0 {
        0
    } else {
        x % y
    }
}

fn main() {
    let _ = remainder_guarded(10, 3);
    let _ = remainder_guarded(10, 0);
}
