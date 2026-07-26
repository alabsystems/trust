// Proof-design fixture: minimal guarded floating-point div-zero obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// floating-point proof surface without std I/O noise.

fn float_divide_guarded(x: f64, y: f64) -> f64 {
    if y == 0.0 {
        0.0
    } else {
        x / y
    }
}

fn main() {
    let _ = float_divide_guarded(10.0, 2.0);
    let _ = float_divide_guarded(10.0, 0.0);
}
