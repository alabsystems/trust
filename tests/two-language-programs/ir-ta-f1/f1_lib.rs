//! F1 hook subject (DESIGN.md Part A step 9): the smallest two-language crate whose entry has
//! a C ABI, so a foreign `main` can call the machine code produced FROM its trust-ir spelling
//! (`-Zcodegen-backend=trust-cg -Ztrust-cg-frontend=trust-ir`). rlib only: trust-cg drops
//! bin/staticlib/cdylib. Not compiled by the default battery — see f1_codegen_hook in run.sh.
pub mod m {
    clean {
        def f1_wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
    }
}
#[inline(never)]
pub fn f1_rust_half(x: u64) -> u64 {
    x ^ 0x55
}
/// Rust -> Lean -> result, exported unmangled. Expected: (5 ^ 0x55) + 7 = 87.
#[unsafe(no_mangle)]
pub extern "C" fn parta_f1_program() -> u64 {
    m::f1_wsum(f1_rust_half(5), 7)
}
