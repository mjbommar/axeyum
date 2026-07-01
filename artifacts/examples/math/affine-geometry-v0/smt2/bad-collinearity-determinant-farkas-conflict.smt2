; QF_LRA/Farkas obstruction for affine-geometry-v0.
;
; Exact affine replay computes that the image triple is collinear, so its
; two-dimensional collinearity determinant is 0. This artifact checks the
; malformed claim that the same determinant is 1.
(set-logic QF_LRA)
(declare-const image_collinearity_determinant Real)
(assert (= image_collinearity_determinant 0))
(assert (= image_collinearity_determinant 1))
(check-sat)
