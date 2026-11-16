//! Native ORACLE for the standalone Lean lane (added by the Part A reviewer).
//! The `clean { }` island below repeats the computational defs of Lib.lean (analyze.py checks
//! the def text is identical modulo whitespace), compiled NATIVELY by the compiler under test;
//! `program()` evaluates exactly what lean_driver.trust_ir evaluates over the standalone-Lean
//! MODULE. So the interpreter's value for the Lean lane is compared with a natively computed
//! number, never with a constant typed twice.
//!   addmul(6,7) + pick(5,9) + lit8(100) [UInt8 wraps: 300 mod 256] + program = 48 + 5 + 44 + 48
// EXPECT: 145
pub mod m {
    clean {
        def addmul (a b : UInt64) : UInt64 := a * b + a
        def pick (a b : UInt64) : UInt64 := a
        def lit8 (a : UInt8) : UInt8 := a + 200
        def program : UInt64 := 48
    }
}
#[inline(never)]
pub fn program() -> u64 {
    m::addmul(6, 7) + m::pick(5, 9) + m::lit8(100) as u64 + m::program()
}
#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
