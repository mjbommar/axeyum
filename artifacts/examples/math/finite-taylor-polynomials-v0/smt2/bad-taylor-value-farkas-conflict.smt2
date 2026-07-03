; Source artifact for finite-taylor-polynomials-v0.
; The trusted resource replay computes taylor_value = 25/4, while the
; malformed row claims taylor_value = 6.
(set-logic QF_LRA)
(declare-const taylor_value Real)
(assert (= taylor_value (/ 25 4)))
(assert (= taylor_value 6))
(check-sat)
