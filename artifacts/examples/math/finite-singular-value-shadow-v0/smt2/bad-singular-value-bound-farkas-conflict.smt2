; QF_LRA/Farkas obstruction for finite-singular-value-shadow-v0.
;
; Exact replay computes sigma_max(A) = 3 for A = [[3,0],[0,1]].
; This artifact checks the malformed claim sigma_max(A) <= 2.
(set-logic QF_LRA)
(declare-const sigma_max Real)
(assert (= sigma_max 3))
(assert (<= sigma_max 2))
(check-sat)
