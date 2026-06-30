; QF_LRA/Farkas obstruction for finite-gradient-descent-v0.
; Exact replay computes decrease_error = 3/4 for the malformed descent row.
(set-logic QF_LRA)
(declare-const decrease_error Real)
(assert (= decrease_error (/ 3 4)))
(assert (= decrease_error 0))
(check-sat)
