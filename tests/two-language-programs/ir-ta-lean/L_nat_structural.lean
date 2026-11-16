-- Part A standalone-Lean refusal probe: nat_structural
def tozero : Nat -> Nat
  | 0 => 0
  | n + 1 => tozero n
