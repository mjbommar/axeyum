; QF_LIA Diophantine obstruction for generating-functions-v0.
;
; For left = [1, 2] and right = [3, 4, 5], the x^2 coefficient of the
; Cauchy product is 1*5 + 2*4 = 13. A claimed x^2 coefficient of 12
; contradicts the same finite coefficient computation.
(set-logic QF_LIA)
(declare-fun term_0_2 () Int)
(declare-fun term_1_1 () Int)
(declare-fun coeff_2 () Int)
(assert (= term_0_2 5))
(assert (= term_1_1 8))
(assert (= coeff_2 (+ term_0_2 term_1_1)))
(assert (= coeff_2 12))
(check-sat)
