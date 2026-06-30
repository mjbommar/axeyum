; QF_LRA/Farkas obstruction for finite-active-set-qp-v0.
; Exact replay computes free_stationarity_error = 2 for the malformed active-set row.
(set-logic QF_LRA)
(declare-const free_stationarity_error Real)
(assert (= free_stationarity_error 2))
(assert (<= free_stationarity_error 0))
(check-sat)
