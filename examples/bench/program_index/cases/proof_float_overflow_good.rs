// Proof-design fixture: minimal guarded floating-point overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// floating-point proof surface without std I/O noise.

const SAFE_LIMIT: f64 = 1.0e300;

fn float_add_guarded(a: f64, b: f64) -> f64 {
    if a > SAFE_LIMIT || a < -SAFE_LIMIT || b > SAFE_LIMIT || b < -SAFE_LIMIT {
        0.0
    } else {
        a + b
    }
}

fn main() {
    let _ = float_add_guarded(1.0, 2.0);
    let _ = float_add_guarded(f64::MAX, 1.0);
}
