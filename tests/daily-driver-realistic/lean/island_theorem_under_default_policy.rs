pub mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
        theorem min2_le_left (a b : UInt64) : min2 a b <= a := by
          unfold min2
          split <;> omega
    }
}
pub fn pick(a: u64, b: u64) -> u64 { m::min2(a, b) }
