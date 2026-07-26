// Proof-design fixture: minimal flawed signed-negation overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn negate_unchecked(x: i32) -> i32 {
    -x
}

fn main() {
    let _ = negate_unchecked(42);
}
