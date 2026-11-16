// A tactic-proof theorem (`unfold`, `split <;> omega`) beside a Rust-callable def,
// in one island. The theorem is stated over `Nat`, where Clean's `omega` has a
// kernel replay; r11 is the `UInt64` twin, still red on omega's UInt64 gap.
mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
        def min2n (a b : Nat) : Nat := if a < b then a else b
        theorem min2n_le_left (a b : Nat) : min2n a b ≤ a := by
          unfold min2n
          split <;> omega
    }
}
fn main() {
    let lo = m::min2(7, 41);
    assert!(lo == 7);
    println!("min2(7,41) = {lo}; min2n_le_left kernel-checked");
}
