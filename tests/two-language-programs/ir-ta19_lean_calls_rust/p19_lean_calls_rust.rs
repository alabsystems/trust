// FEATURE two_lang.lean_calls_rust — Lean -> Rust (RustCallChain), then Rust -> Lean.
// EXPECT: 80
#[inline(never)]
pub fn rx55(x: u64) -> u64 { x ^ 0x55 }
clean {
    def thrice_rx (x : UInt64) : UInt64 := rx55 (rx55 (rx55 x))
}
pub fn program() -> u64 {
    thrice_rx(5)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
