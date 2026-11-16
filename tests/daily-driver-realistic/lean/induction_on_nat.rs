pub mod m { clean {
    def dbl (n : Nat) : Nat := match n with | 0 => 0 | Nat.succ k => Nat.succ (Nat.succ (dbl k))
    theorem dbl_eq (n : Nat) : dbl n = 2 * n := by
      induction n with
      | zero => rfl
      | succ k ih => unfold dbl; omega
} }
