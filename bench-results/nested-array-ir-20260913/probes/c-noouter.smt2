(set-logic ALIA)
(declare-fun m () (Array Int Int))
(assert (= (select m 0) 1))
(check-sat)
