// Proof-design fixture: minimal flawed signed-division overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn signed_divide_unchecked(x: i32, y: i32) -> i32 {
    x / y
}

fn main() {
    let _ = signed_divide_unchecked(10, 2);
}
