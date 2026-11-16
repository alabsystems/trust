-- well-founded (fuelled) recursion over Nat; shape of battery row r03
def gcdF (f a b : Nat) : Nat := if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a
termination_by f
