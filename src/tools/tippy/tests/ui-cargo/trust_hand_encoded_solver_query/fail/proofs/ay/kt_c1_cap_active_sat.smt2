; CONTROL (non-vacuity): the cap is reachable.
(set-logic QF_LIA)
(declare-const b Int)
(assert (and (>= b 0) (= (ite (<= b 4096) b 4096) 4096)))
(check-sat)
; EXPECT: sat
