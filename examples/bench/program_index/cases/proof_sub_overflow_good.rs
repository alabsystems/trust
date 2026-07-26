// Proof-design fixture: minimal guarded subtraction-overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn subtract_guarded(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        0
    }
}

fn main() {
    let _ = subtract_guarded(10, 3);
    let _ = subtract_guarded(3, 10);
}
