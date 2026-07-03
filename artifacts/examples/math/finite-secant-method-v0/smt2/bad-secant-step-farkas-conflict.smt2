; Source artifact for finite-secant-method-v0.
; The trusted resource replay computes secant_next = 4/3, while the
; malformed row claims secant_next = 3/2.
(set-logic QF_LRA)
(declare-const secant_next Real)
(assert (= secant_next (/ 4 3)))
(assert (= secant_next (/ 3 2)))
(check-sat)
