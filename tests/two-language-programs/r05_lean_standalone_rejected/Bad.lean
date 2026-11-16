def triple (n : Nat) : Nat := n + n
theorem triple_eq (n : Nat) : triple n = 3 * n := by
  simp [triple]
