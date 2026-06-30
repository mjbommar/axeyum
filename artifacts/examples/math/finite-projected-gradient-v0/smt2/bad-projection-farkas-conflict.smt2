; QF_LRA/Farkas obstruction for finite-projected-gradient-v0.
; Exact replay rejects claimed_projected_x = 3/2 as feasible for [0,1].
(set-logic QF_LRA)
(declare-const claimed_projected_x Real)
(assert (= claimed_projected_x (/ 3 2)))
(assert (<= claimed_projected_x 1))
(check-sat)
