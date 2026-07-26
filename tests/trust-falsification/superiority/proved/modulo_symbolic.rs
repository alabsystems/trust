#![crate_type = "lib"]
// Wrapping/ring-buffer access `s[n % s.len()]` under a non-empty guard. The
// `!is_empty()` guard discharges the remainder-by-zero check, and the unsigned
// modulo bound `s.len() != 0 ⟹ n % s.len() < s.len()` discharges the index — so
// default mode fully proves it (vs rustc's retained panic branch). The modulus is
// SYMBOLIC (the slice length): the bound is supplied by vcgen and the `mod` term
// that ay cannot handle is dropped by the bridge's sound nonlinear-relaxation retry.
pub fn modulo_symbolic(s: &[u8], n: usize) -> u8 {
    if s.is_empty() {
        0
    } else {
        let k = n % s.len();
        s[k]
    }
}
