; Source artifact for finite-barycentric-interpolation-v0.
; The trusted resource replay computes barycentric_value = 4, while the
; malformed row claims barycentric_value = 5.
(set-logic QF_LRA)
(declare-const barycentric_value Real)
(assert (= barycentric_value 4))
(assert (= barycentric_value 5))
(check-sat)
