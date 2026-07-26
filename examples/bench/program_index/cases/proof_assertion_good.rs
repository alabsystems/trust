// Proof-design fixture: minimal guarded assertion obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// assertion surface without std I/O noise.

fn require_nonnegative_guarded(x: i32) -> i32 {
    if x >= 0 {
        assert!(x >= 0);
        x
    } else {
        0
    }
}

fn main() {
    let _ = require_nonnegative_guarded(4);
    let _ = require_nonnegative_guarded(-1);
}
