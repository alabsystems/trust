// Proof-design fixture: minimal guarded signed-negation overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn negate_guarded(x: i32) -> i32 {
    if x == i32::MIN {
        i32::MAX
    } else {
        -x
    }
}

fn main() {
    let _ = negate_guarded(42);
    let _ = negate_guarded(i32::MIN);
}
