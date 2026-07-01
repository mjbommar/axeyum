; QF_LRA/Farkas obstruction for finite-separation-v0.
;
; Exact convex-combination replay computes x-coordinate error 1/6 for
; the malformed point row.
(set-logic QF_LRA)
(declare-const point_x_error Real)
(assert (= point_x_error (/ 1 6)))
(assert (= point_x_error 0))
(check-sat)
