-- F-131 negative twin `p19_false_theorem` of the 2026-09-17 proof program (Part A-Lean), at the
-- CHECKER level: `targo trust check` must REJECT a `:= rfl` proof of a false equation, naming the
-- declaration (`dbl_wrong` did not elaborate). The judge row ir-tl19_false_theorem pins the same
-- file's refusal on the EMIT lane (`targo trust build --emit=trust-ir`); r05 is the tactic-proof
-- (`unsolved goals`) rejection. Byte-identical to ir-tl19_false_theorem/p19_false_theorem.lean
-- below this header.
def dbl (a : UInt64) : UInt64 := a + a
theorem dbl_wrong (a : UInt64) : dbl a = a := rfl
