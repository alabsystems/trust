// A tactic-proof theorem beside a def in one island (ASCII operators only).
mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
        theorem min2_le_left (a b : UInt64) : min2 a b <= a := by
          unfold min2
          split <;> omega
    }
}
fn main() {
    let lo = m::min2(7, 41);
    assert!(lo == 7);
    println!("min2(7,41) = {lo}");
}
