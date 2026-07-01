; QF_LRA/Farkas obstruction for affine-geometry-v0.
;
; Exact affine replay computes T((A+B)/2) = (6, 4).
; This artifact checks the malformed claim that the y-coordinate is 5.
(set-logic QF_LRA)
(declare-const image_midpoint_y Real)
(assert (= image_midpoint_y 4))
(assert (= image_midpoint_y 5))
(check-sat)
