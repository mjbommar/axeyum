; QF_LRA/Farkas obstruction for finite-walsh-hadamard-transform-v0.
;
; Exact replay computes the second coefficient of H*[1,2,-1,0] as -2.
; This artifact checks the malformed claim that the same coefficient is -1.
(set-logic QF_LRA)
(declare-const transform_coefficient_1 Real)
(assert (= transform_coefficient_1 (- 2.0)))
(assert (= transform_coefficient_1 (- 1.0)))
(check-sat)
