(set-logic QF_LIA)
(declare-fun k () Int)
(assert (= (* 2 k) 1))
(check-sat)
