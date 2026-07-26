// Proof-design fixture: minimal guarded signed-division overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn signed_divide_guarded(x: i32, y: i32) -> i32 {
    if y == 0 || (x == i32::MIN && y == -1) {
        0
    } else {
        x / y
    }
}

fn main() {
    let _ = signed_divide_guarded(10, 2);
    let _ = signed_divide_guarded(10, 0);
    let _ = signed_divide_guarded(i32::MIN, -1);
}
