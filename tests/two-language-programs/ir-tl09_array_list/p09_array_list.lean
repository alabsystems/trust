def sumList : List UInt64 → UInt64
  | [] => 0
  | x :: xs => x + sumList xs
def sumThree (a b c : UInt64) : UInt64 := sumList [a, b, c]
def arrSize (a b : UInt64) : Nat := (#[a, b, a]).size
