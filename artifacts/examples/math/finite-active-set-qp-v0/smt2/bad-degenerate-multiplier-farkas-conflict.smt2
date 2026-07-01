; QF_LRA/Farkas obstruction for finite-active-set-qp-v0.
; Exact replay computes stationarity_error = 1 for the malformed positive
; multiplier on a degenerate active bound.
(set-logic QF_LRA)
(declare-const degenerate_stationarity_error Real)
(assert (= degenerate_stationarity_error 1))
(assert (= degenerate_stationarity_error 0))
(check-sat)
