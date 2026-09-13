(set-logic ALIA)
(declare-fun m () (Array Int (Array Int Int)))
(assert (forall ((q (Array Int (Array Int Int)))) (= (select q 0) (select m 0))))
(check-sat)
