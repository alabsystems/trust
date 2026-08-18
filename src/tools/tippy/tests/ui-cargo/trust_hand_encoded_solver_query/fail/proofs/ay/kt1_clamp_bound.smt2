; THEOREM: the kept tail never exceeds the cap, for every budget.
; Negation asserted; UNSAT == proved for ALL b >= 0.
(set-logic QF_LIA)
(declare-const b Int)
(assert (>= b 0))
(assert (let ((kept (ite (<= b 4096) b 4096)))
          (> kept 4096)))
(check-sat)
; EXPECT: unsat
