; QF_LRA/Farkas obstruction for finite-wolfe-line-search-v0.
; Exact replay computes sufficient-decrease slack = 1/2 for the accepted step.
(set-logic QF_LRA)
(declare-const sufficient_decrease_slack Real)
(assert (= sufficient_decrease_slack (/ 1 2)))
(assert (<= sufficient_decrease_slack 0))
(check-sat)
