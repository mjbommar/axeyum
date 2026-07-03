; Source artifact for finite-aitken-acceleration-v0.
; The trusted resource replay computes aitken_value = 1, while the
; malformed row claims aitken_value = 3/2.
(set-logic QF_LRA)
(declare-const aitken_value Real)
(assert (= aitken_value 1))
(assert (= aitken_value (/ 3 2)))
(check-sat)
