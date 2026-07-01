; QF_LRA/Farkas obstruction for finite-gradient-descent-v0.
; Exact replay computes descent_slack = 1/4 for the malformed descent-bound row.
(set-logic QF_LRA)
(declare-const descent_slack Real)
(assert (= descent_slack (/ 1 4)))
(assert (<= descent_slack 0))
(check-sat)
