// FEATURE lean.inductive_match (wrapped half) — a machine-width def whose body
// EXPECT: 2
// goes THROUGH the inductive (no inductive value crosses the language seam).
pub mod m {
    clean {
        inductive Tri where
          | one : Tri
          | two : Tri
          | three : Tri

        def triRank (t : Tri) : UInt64 :=
          match t with
          | Tri.one => 1
          | Tri.two => 2
          | Tri.three => 3

        def rankOfTwo (x : UInt64) : UInt64 := triRank Tri.two
    }
}
pub fn program() -> u64 {
    m::rankOfTwo(0)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
