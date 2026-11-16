mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
        theorem min2_ge_left (a b : UInt64) : a <= min2 a b := by
          unfold min2
          split <;> omega
    }
}
fn main() { let _ = m::min2(7, 41); }
