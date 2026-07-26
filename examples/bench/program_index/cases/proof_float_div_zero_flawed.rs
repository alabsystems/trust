// Proof-design fixture: minimal flawed floating-point div-zero obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// floating-point proof surface without std I/O noise.

fn float_divide_unchecked(x: f64, y: f64) -> f64 {
    x / y
}

fn main() {
    let _ = float_divide_unchecked(10.0, 2.0);
}
