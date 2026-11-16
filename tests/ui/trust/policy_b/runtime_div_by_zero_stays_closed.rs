//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The B != advisory pin. A REFUTED obligation is fatal under the default policy —
//! only a gap that keeps rustc's runtime check is tolerated. `10 / z` with a
//! runtime `z` is refuted with a counterexample (z = 0) and must not build.
fn main() {
    let z = std::hint::black_box(0u32);
    println!("{}", 10 / z);
}
