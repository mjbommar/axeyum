; QF_LRA/Farkas obstruction for rigid-configuration-geometry-v0.
;
; Exact translation replay computes (3,0) + (1,-2) = (4,-2).
; This artifact checks the malformed claim that the translated x-coordinate is 5.
(set-logic QF_LRA)
(declare-const target_b_x Real)
(assert (= target_b_x 4))
(assert (= target_b_x 5))
(check-sat)
