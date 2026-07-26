// Proof-design fixture: minimal flawed division-by-zero obligation.
//
// The benchmark keeps this case free of formatting and allocation so the
// trust-verify slot measures the arithmetic proof surface rather than std I/O.

fn divide_unchecked(x: u32, y: u32) -> u32 {
    x / y
}

fn main() {
    let _ = divide_unchecked(10, 2);
}
