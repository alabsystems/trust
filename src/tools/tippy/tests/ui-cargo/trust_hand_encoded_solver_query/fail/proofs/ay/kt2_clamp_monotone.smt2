; THEOREM: the clamp is monotone in the budget.
(set-logic QF_LIA)
(declare-const b1 Int)
(declare-const b2 Int)
(assert (and (>= b1 0) (>= b2 b1)))
(assert (> (ite (<= b1 4096) b1 4096) (ite (<= b2 4096) b2 4096)))
(check-sat)
; EXPECT: unsat
