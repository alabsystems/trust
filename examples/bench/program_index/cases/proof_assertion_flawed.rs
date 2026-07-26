// Proof-design fixture: minimal flawed assertion obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// assertion surface without std I/O noise.

fn require_nonnegative(x: i32) -> i32 {
    assert!(x >= 0);
    x
}

fn main() {
    let _ = require_nonnegative(4);
}
