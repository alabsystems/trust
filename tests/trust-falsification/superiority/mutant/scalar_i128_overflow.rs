#![crate_type = "lib"]
// SOUNDNESS REGRESSION (128-bit false proof, found by the adversarial false-proof hunt).
// An unguarded i128 multiply can overflow (i128::MAX * 2), so it must NOT be statically
// eliminated. Previously FALSE-PROVED: for signed width 128 the type max IS the solver's
// representable ceiling, so the Int-path overflow check `result > i128::MAX` is vacuously
// unsatisfiable. The fix fail-closes signed width>=128 arithmetic to a runtime check, so
// this stays NOT fully discharged. If it ever becomes fully proved, the 128-bit overflow
// soundness hole has regressed.
pub fn f(a: i128, b: i128) -> i128 {
    a * b
}
