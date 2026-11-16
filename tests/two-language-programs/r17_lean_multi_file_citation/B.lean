-- B cites A's theorem; the two files are one resolution unit.
def twice (n : Nat) : Nat := base (base n)
theorem twice_eq (n : Nat) : twice n = base n + 1 := base_eq (base n)
