; Source artifact for finite-cubic-hermite-interpolation-v0.
; The trusted resource replay computes hermite_value = 7/4, while the
; malformed row claims hermite_value = 2.
(set-logic QF_LRA)
(declare-const hermite_value Real)
(assert (= hermite_value (/ 7 4)))
(assert (= hermite_value 2))
(check-sat)
