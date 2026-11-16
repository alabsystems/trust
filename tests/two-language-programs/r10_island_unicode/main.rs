// Lean source is Unicode; the island must accept it (operators, primes, ⟨⟩, λ).
// `imp_self'`, not `imp_self`: the island elaborates over Lean 4.8.0's core, which
// declares `imp_self`, and since pin train T1's Clean move (`4711072a3a4`) a
// redeclaration is refused ("`imp_self` has already been declared (Lean 4.8.0
// core)"). What this row tests is Unicode in an island, not that name. T1 made the
// same rename in tests/ui/trust/clean_island_lexical_unicode.rs and missed this row.
mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
        theorem le_self (n : Nat) : n ≤ n := Nat.le_refl n
        theorem all_refl : ∀ n : Nat, n = n := fun n => rfl
        theorem imp_self' (p : Prop) : p → p := λ h => h
        theorem conj (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
        def id' (a : UInt64) : UInt64 := a
        theorem id'_eq (h' : 0 = 0) (a : UInt64) : id' a = a := rfl
    }
}
fn main() {
    let lo = m::min2(7, 41);
    assert!(lo == 7);
    println!("min2(7,41) = {lo}");
}
