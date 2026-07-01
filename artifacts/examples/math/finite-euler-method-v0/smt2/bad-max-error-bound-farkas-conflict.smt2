; QF_LRA/Farkas obstruction for finite-euler-method-v0.
;
; Exact replay computes max error 3/4 for the finite Euler table.
; This artifact checks the malformed claim that the same max error is <= 1/2.
(set-logic QF_LRA)
(declare-const max_error Real)
(assert (= max_error (/ 3 4)))
(assert (<= max_error (/ 1 2)))
(check-sat)
