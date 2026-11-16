// Negative twin of two_lang.citation: the clause is TRUE, but the cited Lean theorem does not
// prove it (it is about `n <= n + n`, not about `rmin2`). The citation must be refused.
clean {
    theorem nat_le_doubled : forall (n : Nat),
        Nat.le n (Nat.add n n) :=
        fun n => Nat.le_add_right n n
}
#[inline(never)]
pub fn rmin2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}
pub fn pick_min(x: u64, y: u64) -> u64
    ensures rmin2(x, y) <= x by nat_le_doubled
{
    rmin2(x, y)
}
