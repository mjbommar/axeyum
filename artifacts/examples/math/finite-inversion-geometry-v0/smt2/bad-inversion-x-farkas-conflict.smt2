; QF_LRA/Farkas obstruction for finite-inversion-geometry-v0.
; Exact replay computes inverse x-coordinate = 2/5 for inversion of (2,1).
(set-logic QF_LRA)
(declare-const inverse_x Real)
(assert (= inverse_x (/ 2 5)))
(assert (= inverse_x (/ 1 2)))
(check-sat)
