; QF_LRA/Farkas obstruction for finite-lanczos-iteration-v0.
;
; Exact replay computes beta1 = ||A*q1 - (q1^T*A*q1)q1|| = 1.
; This artifact checks the malformed claim that the same coefficient is 2.
(set-logic QF_LRA)
(declare-const lanczos_beta1 Real)
(assert (= lanczos_beta1 1))
(assert (= lanczos_beta1 2))
(check-sat)
