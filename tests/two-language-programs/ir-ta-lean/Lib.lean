-- Part A standalone Lean lane: the library file. Every computational declaration is inside
-- the admitted standalone fragment (UIntN wrapping +,-,* trees, projection, literal), because
-- the lane is ALL-OR-NOTHING: one refused sibling refuses the whole artifact.
def addmul (a b : UInt64) : UInt64 := a * b + a
def pick (a b : UInt64) : UInt64 := a
def lit8 (a : UInt8) : UInt8 := a + 200
def program : UInt64 := 48
theorem pick_eq (a b : UInt64) : pick a b = a := rfl
