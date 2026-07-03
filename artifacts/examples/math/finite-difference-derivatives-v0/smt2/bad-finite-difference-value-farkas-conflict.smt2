; Source artifact for finite-difference-derivatives-v0.
; The trusted resource replay computes finite_difference_value = 4, while the
; malformed row claims finite_difference_value = 5.
(set-logic QF_LRA)
(declare-const finite_difference_value Real)
(assert (= finite_difference_value 4))
(assert (= finite_difference_value 5))
(check-sat)
