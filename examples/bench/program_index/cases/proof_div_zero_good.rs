// Proof-design fixture: minimal guarded division-by-zero obligation.
//
// The benchmark keeps this case free of formatting and allocation so the
// trust-verify slot measures the arithmetic proof surface rather than std I/O.

fn divide_guarded(x: u32, y: u32) -> u32 {
    if y == 0 {
        0
    } else {
        x / y
    }
}

fn main() {
    let _ = divide_guarded(10, 2);
    let _ = divide_guarded(10, 0);
}
