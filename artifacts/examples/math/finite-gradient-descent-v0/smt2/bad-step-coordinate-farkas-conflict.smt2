; QF_LRA/Farkas obstruction for finite-gradient-descent-v0.
; Exact replay computes next_x = 1/2 for the malformed step-coordinate row.
(set-logic QF_LRA)
(declare-const next_x Real)
(assert (= next_x (/ 1 2)))
(assert (= next_x (/ 3 4)))
(check-sat)
