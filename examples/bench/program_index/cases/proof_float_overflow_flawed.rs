// Proof-design fixture: minimal flawed floating-point overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// floating-point proof surface without std I/O noise.

fn float_add_unchecked(a: f64, b: f64) -> f64 {
    a + b
}

fn main() {
    let _ = float_add_unchecked(1.0, 2.0);
}
