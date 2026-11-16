-- Bool connective over two comparisons (DESIGN Part A: "Bool comparison + connective")
def both (a b c : UInt64) : Bool := a < b && b < c
