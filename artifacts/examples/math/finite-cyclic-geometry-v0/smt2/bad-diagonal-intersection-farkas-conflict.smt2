; QF_LRA/Farkas obstruction for finite-cyclic-geometry-v0.
; Exact replay computes diagonal intersection x-coordinate = 0.
(set-logic QF_LRA)
(declare-const diagonal_intersection_x Real)
(assert (= diagonal_intersection_x 0))
(assert (= diagonal_intersection_x (/ 1 2)))
(check-sat)
