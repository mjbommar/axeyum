; Source artifact for finite-cubic-spline-interpolation-v0.
; The trusted resource replay computes spline_value = 11/16, while the
; malformed row claims spline_value = 3/4.
(set-logic QF_LRA)
(declare-const spline_value Real)
(assert (= spline_value (/ 11 16)))
(assert (= spline_value (/ 3 4)))
(check-sat)
