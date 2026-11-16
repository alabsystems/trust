// FEATURE lean.inductive_match (module half) — an `inductive` and a `match` over it
// EXPECT: 2
// (tier general), declared beside a callable def. Rust does NOT call `triRank` here, so
// this probe measures only whether the general-tier body reaches the module.
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

        def keep (a : UInt64) (b : UInt64) : UInt64 := a
    }
}
pub fn program() -> u64 {
    m::keep(2, 9)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
