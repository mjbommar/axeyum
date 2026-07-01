; QF_LRA/Farkas obstruction for finite-kkt-v0.
;
; Exact KKT replay computes complementarity = 0 for multiplier 2 at x = 1
; because the active constraint value is 0. The malformed row claims
; complementarity = 1, so the error is 1. It also requires that error to be 0.
(set-logic QF_LRA)
(declare-const complementarity_error Real)
(assert (= complementarity_error 1))
(assert (= complementarity_error 0))
(check-sat)
