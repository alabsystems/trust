(set-logic QF_LIA)
(declare-const x Int)
(assert (and (> x 0) (< x 0)))
(check-sat)
