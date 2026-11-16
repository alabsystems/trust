-- Negative twin for the standalone Lean lane: a FALSE theorem must be REJECTED.
def pick (a b : UInt64) : UInt64 := a
theorem pick_wrong (a b : UInt64) : pick a b = b := rfl
