; QF_LRA/Farkas obstruction for finite-conjugate-gradient-v0.
;
; Exact replay computes alpha0 = (r0^T r0) / (p0^T A p0) = 5/20 = 1/4.
; This artifact checks the malformed claim that the same step size is 1/3.
(set-logic QF_LRA)
(declare-const cg_alpha0 Real)
(assert (= cg_alpha0 (/ 1 4)))
(assert (= cg_alpha0 (/ 1 3)))
(check-sat)
