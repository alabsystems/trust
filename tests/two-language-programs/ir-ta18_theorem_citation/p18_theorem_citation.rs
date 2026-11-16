// FEATURE two_lang.citation — a Lean theorem, and a Rust `ensures … by thm` citing it.
// EXPECT: 7
clean {
    theorem min2_le_left : forall (x : UInt64) (y : UInt64),
        Nat.le (UInt64.toNat (if x < y then x else y)) (UInt64.toNat x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt x y)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => y) (fun _ => x))) (UInt64.toNat x))
            (instDecidableUInt64Lt x y)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat x) (UInt64.toNat y)) h)
            (fun h => Nat.le.refl (UInt64.toNat x))
}
#[inline(never)]
pub fn rmin2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}
#[inline(never)]
pub fn pick_min(x: u64, y: u64) -> u64
    ensures rmin2(x, y) <= x by min2_le_left
{
    rmin2(x, y)
}
pub fn program() -> u64 {
    pick_min(41, 7)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
