// FEATURE lean.inductive_match (call half) — Rust builds a Lean inductive value and
// EXPECT: 2
// calls the matching def: the Lean-inductive <-> Rust-enum carrier.
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
    }
}
pub fn program() -> u64 {
    m::triRank(m::Tri::two)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
