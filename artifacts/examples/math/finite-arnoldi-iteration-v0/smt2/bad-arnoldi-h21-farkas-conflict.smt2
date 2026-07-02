; QF_LRA/Farkas obstruction for finite-arnoldi-iteration-v0.
;
; Exact replay computes h21 = ||A*q1 - (q1^T*A*q1)q1|| = 3.
; This artifact checks the malformed claim that the same coefficient is 2.
(set-logic QF_LRA)
(declare-const arnoldi_h21 Real)
(assert (= arnoldi_h21 3))
(assert (= arnoldi_h21 2))
(check-sat)
