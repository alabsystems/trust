-- Part A standalone-Lean refusal probe: nat_wf
def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0
termination_by n
