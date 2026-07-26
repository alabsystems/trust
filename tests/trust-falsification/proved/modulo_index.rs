#![crate_type = "lib"]
// A modulo index into a fixed-size array, `s[i % 8]` on `[i32; 8]`. rustc keeps a
// runtime bounds check; Trust discharges it STATICALLY. vcgen conjoins the modulo
// result-bound fact `Or([8 = 0, i%8 < 8])` (the remainder is `< 8` unless the
// divisor is 0); with the violation `i%8 >= 8` the clean CIC kernel certifies it
// by Or.rec case-split — the `8 = 0` branch is a closed-false equality, the
// `i%8 < 8` branch chains against `i%8 >= 8` (`8 <= _3 < 8 ⊢ 8 < 8`). The divisor
// 8 equals the array length, so every `i % 8` is in bounds. -full kernel-Certified.
pub fn modulo_index(s: &[i32; 8], i: usize) -> i32 {
    s[i % 8]
}
