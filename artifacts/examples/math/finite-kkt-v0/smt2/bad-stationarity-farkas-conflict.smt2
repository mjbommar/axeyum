; QF_LRA/Farkas obstruction for finite-kkt-v0.
;
; Exact KKT replay computes stationarity_residual = -1 for multiplier 1 at
; x = 1, so the error from the claimed zero residual is 1. The malformed row
; also requires that error to be 0.
(set-logic QF_LRA)
(declare-const stationarity_error Real)
(assert (= stationarity_error 1))
(assert (= stationarity_error 0))
(check-sat)
