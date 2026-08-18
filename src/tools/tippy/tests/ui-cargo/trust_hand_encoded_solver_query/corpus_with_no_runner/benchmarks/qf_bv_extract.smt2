(set-logic QF_BV)
(declare-const w (_ BitVec 32))
(assert (distinct ((_ extract 7 0) w) ((_ extract 7 0) w)))
(check-sat)
