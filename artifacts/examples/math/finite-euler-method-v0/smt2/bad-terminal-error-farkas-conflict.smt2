; QF_LRA/Farkas obstruction for finite-euler-method-v0.
;
; Exact replay computes terminal_error = |9/4 - 3/2| = 3/4.
; The malformed row claims the same terminal error is 1/2.
(set-logic QF_LRA)
(declare-const terminal_error Real)
(assert (= terminal_error (/ 3 4)))
(assert (= terminal_error (/ 1 2)))
(check-sat)
