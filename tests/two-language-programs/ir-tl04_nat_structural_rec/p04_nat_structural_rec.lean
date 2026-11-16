def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
