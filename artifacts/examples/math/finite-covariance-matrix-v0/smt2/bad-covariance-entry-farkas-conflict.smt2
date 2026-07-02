; QF_LRA/Farkas obstruction for finite-covariance-matrix-v0.
;
; Exact replay computes the off-diagonal covariance entry as 4/9.
; This artifact checks the malformed claim that the same entry is 1/2.
(set-logic QF_LRA)
(declare-const covariance_01 Real)
(assert (= covariance_01 (/ 4 9)))
(assert (= covariance_01 (/ 1 2)))
(check-sat)
