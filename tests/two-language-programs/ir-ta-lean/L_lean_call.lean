-- Part A standalone-Lean refusal probe: lean_call
def inc (a : UInt64) : UInt64 := a + 1
def inc2 (a : UInt64) : UInt64 := inc (inc a)
